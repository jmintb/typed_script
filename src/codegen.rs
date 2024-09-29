use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap},
};

use anyhow::{bail, Result};

use melior::{
    dialect::{
        arith,
        func::{self},
        index,
        llvm::{self, attributes::Linkage},
        memref, scf, DialectRegistry,
    },
    ir::{
        attribute::{
            DenseI64ArrayAttribute, FlatSymbolRefAttribute, IntegerAttribute, StringAttribute,
            TypeAttribute,
        },
        operation::OperationBuilder,
        r#type::{FunctionType, IntegerType, MemRefType},
        Attribute, Block, Identifier, Location, Module, Operation, OperationRef, Region, Type,
        Value, ValueLike,
    },
    pass,
    utility::{register_all_dialects, register_all_llvm_translations},
    Context, ExecutionEngine,
};

use crate::{
    parser::{FunctionKeyword, TSIdentifier, TSValue},
    typed_ast::{
        self, Array, ArrayLookup, Assign, Assignment, Decl, IfStatement, Return, StructType,
        TypedAst, TypedExpression, TypedProgram, While,
    }, ir::IrProgram,
};

// TODO: something inside the module is dropped when it is returned.
// That is why we return the exection engine at the moment.

struct CodeGen<'ctx, 'module> {
    context: &'ctx Context,
    module: &'module Module<'ctx>,
    annon_string_counter: RefCell<usize>,
    type_store: BTreeMap<TSIdentifier, typed_ast::Type>,
    var_to_type: HashMap<TSIdentifier, typed_ast::Type>,
}

impl<'ctx, 'module> CodeGen<'ctx, 'module> {
    fn new(
        context: &'ctx Context,
        module: &'module Module<'ctx>,
        types: BTreeMap<TSIdentifier, typed_ast::Type>,
        variable_types: HashMap<TSIdentifier, typed_ast::Type>,
    ) -> Self {
        Self {
            context,
            module,
            annon_string_counter: 0.into(),
            type_store: types,
            var_to_type: variable_types,
        }
    }

    fn gen_annon_string_id(&self) -> String {
        let id = format!("annonstr{}", self.annon_string_counter.borrow());

        self.annon_string_counter
            .replace_with(|&mut v| v + 1 as usize);

        id
    }

    fn gen_declaration<'a>(&'a self, decl: Decl, _: Location<'a>) -> Result<Operation>
    where
        'a: 'ctx,
    {
        match decl {
            e @ Decl::Function { .. } => self.gen_function(e),
            _ => todo!("struct decl"),
        }
    }

    fn gen_function(&self, decl: Decl) -> Result<Operation> {
        let Decl::Function {
            keywords,
            id,
            arguments,
            body,
            return_type,
        } = decl
        else {
            panic!("recieved a non function declaration");
        };


        let argument_types = arguments
            .iter()
            .map(|arg_type| arg_type.r#type.as_mlir_type(self.context, &self.type_store))
            .collect::<Vec<Type<'ctx>>>();
        let _mlir_return_type = return_type.as_mlir_type(self.context, &self.type_store);

        let function_region = Region::new();
        let location = melior::ir::Location::unknown(self.context);

        // TODO: use memref for one shot bufferization optimisations.
        let function_block = Block::new(
            argument_types
                .clone()
                .into_iter()
                .map(|arg_type| (arg_type, location))
                .collect::<Vec<(Type, Location)>>()
                .as_slice(),
        );

        let mut variable_store: HashMap<TSIdentifier, Value<'ctx, '_>> = HashMap::new();

        for (position, argument) in arguments.iter().enumerate() {
            let value_ref = function_block.argument(position).expect(&format!(
                "expected at least {} function arguments for fn: {}",
                position, id.0,
            ));

            let ptr = function_block
                .append_operation(memref::alloca(
                    self.context,
                    MemRefType::new(value_ref.r#type(), &[], None, None),
                    &[],
                    &[],
                    None,
                    location,
                ))
                .result(0)
                .unwrap();

            function_block.append_operation(memref::store(
                value_ref.into(),
                ptr.into(),
                &[],
                location,
            ));

            variable_store.insert(argument.name.clone(), ptr.into());
        }

        if let Some(body) = body {
            self.gen_statements(body, &function_block, &mut variable_store, true)?;
            function_region.append_block(function_block);
        }

        let functiom_decl = if &id.0 == "main" {
            func::func(
                &self.context,
                StringAttribute::new(&self.context, &id.0),
                TypeAttribute::new(
                    FunctionType::new(
                        &self.context,
                        arguments
                            .iter()
                            .map(|_| llvm::r#type::opaque_pointer(&self.context).into())
                            .collect::<Vec<Type>>()
                            .as_slice(),
                        &[],
                    )
                    .into(),
                ),
                function_region,
                &[(
                    Identifier::new(&self.context, "llvm.emit_c_interface"),
                    Attribute::unit(&self.context),
                )],
                location,
            )
        } else if keywords.contains(&FunctionKeyword::LlvmExtern) {
            llvm::func(
                &self.context,
                StringAttribute::new(&self.context, &id.0),
                TypeAttribute::new(
                    llvm::r#type::function(
                        return_type.as_mlir_type(&self.context, &self.type_store),
                        arguments
                            .iter()
                            .map(|a| a.r#type.as_mlir_type(&self.context, &self.type_store))
                            .collect::<Vec<Type>>()
                            .as_slice(),
                        false,
                    )
                    .into(),
                ),
                function_region,
                &[
                    (
                        Identifier::new(&self.context, "sym_visibility"),
                        StringAttribute::new(&self.context, "private").into(),
                    ),
                    (
                        Identifier::new(&self.context, "llvm.emit_c_interface"),
                        Attribute::unit(&self.context),
                    ),
                ],
                location,
            )
        } else {
            func::func(
                &self.context,
                StringAttribute::new(&self.context, &id.0),
                TypeAttribute::new(
                    FunctionType::new(
                        &self.context,
                        &argument_types,
                        &[return_type.as_mlir_type(&self.context, &self.type_store)],
                    )
                    .into(),
                ),
                function_region,
                &[],
                location,
            )
        };

        Ok(functiom_decl)
    }

    fn gen_ast_code(&'ctx self, ast: TypedProgram, _emit_mlir: bool) -> Result<()> {
        let location = Location::unknown(&self.context);

        for node in ast.ast {
            match node.clone() {
                TypedAst::Decl(ref d @ Decl::Function { .. }) => {
                    let function_decl = self.gen_declaration(d.clone(), location)?;

                    self.module.body().append_operation(function_decl);
                }
                TypedAst::Decl(Decl::Struct(..)) => {}
                _ => todo!(),
            }
        }

        Ok(())
    }

    fn gen_block(
        &self,
        block: typed_ast::Block,
        variable_store: &mut HashMap<TSIdentifier, Value<'ctx, '_>>,
    ) -> Result<(Region<'ctx>, Option<Type<'ctx>>)> {
        // TODO: should it really be necessary to clone variable store here?
        let builder = Block::new(&[]);
        let mut variable_store = variable_store.clone();
        // TODO: should split variable scope here.

        let _ = self.gen_statements(block.statements, &builder, &mut variable_store, false);

        let region = Region::new();
        region.append_block(builder);

        Ok((region, None))
    }

    // TODO: Switch to btreemap


    fn gen_statements<'a>(
        &self,
        nodes: Vec<TypedAst>,
        current_block: &'a Block<'ctx>,
        variable_store: &mut HashMap<TSIdentifier, Value<'ctx, 'a>>,
        function_scope: bool,
    ) -> Result<()> {
        let location = melior::ir::Location::unknown(self.context);

        for node in nodes {
            match node {
                TypedAst::Expression(exp) => {
                    let _ = self.gen_expression_code(exp, current_block, variable_store)?;
                }
                TypedAst::Decl(_decl) => {
                    todo!("we do not support declarations inside functions yet");
                }
                TypedAst::Assignment(assignment) => {
                    self.gen_assignment_code(assignment, current_block, variable_store)?;
                }
            }
        }

        if !function_scope {
            current_block.append_operation(scf::r#yield(&[], location));
        }

        Ok(())
    }

    fn gen_assignment_code<'a>(
        &self,
        assignment: Assignment,
        current_block: &'a Block<'ctx>,
        variable_store: &mut HashMap<TSIdentifier, Value<'ctx, 'a>>,
    ) -> Result<()> {
        let initial_value =
            self.gen_expression_code(assignment.expression.clone(), current_block, variable_store)?;

        if let Some(initial_value) = initial_value {
            let ptr = melior::dialect::memref::alloca(
                self.context,
                MemRefType::new(initial_value.r#type(), &[], None, None),
                &[],
                &[],
                None,
                Location::unknown(self.context),
            );
            let ptr_val = current_block.append_operation(ptr).result(0).unwrap();
            let store_op = melior::dialect::memref::store(
                initial_value,
                ptr_val.into(),
                &[],
                melior::ir::Location::unknown(self.context),
            );

            current_block.append_operation(store_op);

            variable_store.insert(assignment.id, ptr_val.into());
        } else {
            bail!(format!(
                "assingment expression did not return a value: {:#?} {:#?}",
                assignment,
                self.type_store.get(&TSIdentifier("fdopen".to_string()))
            ));
        }

        Ok(())
    }

    fn gen_assign_code<'a>(
        &self,
        assign: Assign,
        current_block: &'a Block<'ctx>,
        variable_store: &mut HashMap<TSIdentifier, Value<'ctx, 'a>>,
    ) -> Result<()> {
        let initial_value =
            self.gen_expression_code(*assign.expression.clone(), current_block, variable_store)?;

        if let Some(initial_value) = initial_value {
            let var_ref = variable_store.get(&assign.id).unwrap();
            let store_op = melior::dialect::memref::store(
                initial_value,
                *var_ref,
                &[],
                melior::ir::Location::unknown(self.context),
            );

            current_block.append_operation(store_op);
        } else {
            bail!(format!(
                "assing expression did not return a value: {:#?} {:#?}",
                assign,
                self.type_store.get(&TSIdentifier("fdopen".to_string()))
            ));
        }

        Ok(())
    }

    fn gen_const_index<'a>(
        &self,
        index: i64,
        current_block: &'a Block<'ctx>,
    ) -> Result<Value<'ctx, 'a>> {
        let location = melior::ir::Location::unknown(self.context);
        Ok(current_block
            .append_operation(index::constant(
                self.context,
                IntegerAttribute::new(index, melior::ir::Type::index(self.context)),
                location,
            ))
            .result(0)?
            .into())
    }

    fn gen_expression_code<'a>(
        &self,
        exp: TypedExpression,
        current_block: &'a Block<'ctx>,
        variable_store: &mut HashMap<TSIdentifier, Value<'ctx, 'a>>,
    ) -> Result<Option<Value<'ctx, 'a>>> {
        let location = melior::ir::Location::unknown(self.context);
        let val: Option<Value> = match exp {
            TypedExpression::Value(TSValue::String(val), _vtype) => {
                // TODO: \n is getting escaped, perhap we need a raw string?
                let val = if val == "\\n" { "\n" } else { &val };
                let val = val.replace("\\n", "\n");

                Some(
                    self.gen_pointer_to_annon_str(current_block, val.to_string())?
                        .result(0)?
                        .into(),
                )
            }
            TypedExpression::Assign(assign) => {
                self.gen_assign_code(assign, current_block, variable_store)?;
                None
            }
            TypedExpression::Value(TSValue::Integer(v), _) => {
                Some(
                    current_block
                        .append_operation(melior::dialect::arith::constant(
                            &self.context,
                            IntegerAttribute::new(
                                v as i64, // TODO why do we need 4 here?
                                IntegerType::new(&self.context, 32).into(),
                            )
                            .into(),
                            location,
                        ))
                        .result(0)?
                        .into(),
                )
            }
            // TODO: enter function arguments into variable store
            TypedExpression::Value(TSValue::Variable(ref id), _type) => {
                if let Some(v) = variable_store.get(id) {
                    let load = current_block
                        .append_operation(memref::load(*v, &[], location))
                        .result(0)?;
                    Some(load.into())
                } else {
                    bail!("Failed to find variable {}", id.0)
                }
            }
            TypedExpression::Call(id, args) => {
                let actual_args = args
                    .iter()
                    .map(|arg| {
                        let operations = self
                            .gen_expression_code(arg.clone(), current_block, variable_store)
                            .unwrap();
                        operations.unwrap()
                    })
                    .collect::<Vec<Value>>();

                let fn_type = self.type_store.get(&id).unwrap();

                let (callee_keywords, return_type) =
                    if let typed_ast::Type::Function(keywords, _, return_type) = fn_type {
                        (keywords, return_type)
                    } else {
                        panic!(
                            "failed to find a function dcelaration or return type for {}",
                            id.0
                        );
                    };

                let call_operation = if callee_keywords.contains(&FunctionKeyword::LlvmExtern) {
                    OperationBuilder::new("func.call", location)
                        .add_operands(&actual_args)
                        .add_attributes(&[(
                            Identifier::new(&self.context, "callee"),
                            FlatSymbolRefAttribute::new(&self.context, &id.0).into(),
                        )])
                        .add_results(&[return_type.as_mlir_type(self.context, &self.type_store)])
                        .build()?
                } else {
                    let return_types = if let typed_ast::Type::Unit = **return_type {
                        Vec::new()
                    } else {
                        vec![return_type.as_mlir_type(self.context, &self.type_store)]
                    };
                    func::call(
                        &self.context,
                        FlatSymbolRefAttribute::new(&self.context, &id.0),
                        &actual_args,
                        &return_types,
                        location,
                    )
                };

                if let Ok(val) = current_block.append_operation(call_operation).result(0) {
                    Some(val.into())
                } else {
                    None
                }
            }
            TypedExpression::If(IfStatement {
                condition,
                then_block,
                else_block,
            }) => {
                let condition = self
                    .gen_expression_code(*condition, current_block, variable_store)?
                    .unwrap();

                let (then_region, _) = self.gen_block(then_block, variable_store)?;

                let else_region = if let Some(else_block) = else_block {
                    self.gen_block(else_block, variable_store)?.0
                } else {
                    Region::new()
                };

                current_block.append_operation(melior::dialect::scf::r#if(
                    condition,
                    &[],
                    then_region,
                    else_region,
                    location,
                ));

                None
            }

            TypedExpression::StructFieldRef(struct_id, field_id) => {
                let struct_type = self.var_to_type.get(&struct_id).unwrap();
                let struct_ptr = variable_store.get(&struct_id).unwrap().to_owned();

                let Some((field_index, field_type)) =
                    (if let typed_ast::Type::Struct(StructType {
                        identifier: _,
                        fields,
                    }) = struct_type
                    {
                        fields
                            .iter()
                            .position(|f| f.field_name == field_id)
                            .map(|pos| (pos, fields[pos].field_type.clone()))
                    } else {
                        bail!(
                            "Expected to find a struct type for variable {} instead found {:#?}",
                            struct_id.0,
                            struct_type
                        );
                    })
                else {
                    bail!(
                        "Failed to find field {} in struct {:?}",
                        field_id.0,
                        struct_type
                    );
                };

                let loaded_ptr = current_block
                    .append_operation(memref::load(struct_ptr, &[], location))
                    .result(0)?;

                let gep = llvm::extract_value(
                    self.context,
                    loaded_ptr.into(),
                    DenseI64ArrayAttribute::new(self.context, &[field_index as i64]),
                    field_type.as_mlir_type(self.context, &self.type_store),
                    location,
                );

                let gep_ref: Value = current_block.append_operation(gep).result(0)?.into();

                Some(gep_ref)
            }
            TypedExpression::Struct(id, fields) => {
                let _size = melior::dialect::arith::constant(
                    &self.context,
                    IntegerAttribute::new(1, IntegerType::new(&self.context, 32).into()).into(),
                    location,
                );

                let typed_ast::Type::Struct(struct_ts_type) = self.type_store.get(&id).unwrap()
                else {
                    todo!()
                };

                let struct_type = llvm::r#type::r#struct(
                    self.context,
                    struct_ts_type
                        .fields
                        .clone()
                        .into_iter()
                        .map(|exp| exp.field_type.as_mlir_type(self.context, &self.type_store))
                        .collect::<Vec<Type>>()
                        .as_slice(),
                    true,
                );

                let mut struct_ptr: Value = current_block
                    .append_operation(llvm::undef(struct_type, location))
                    .result(0)?
                    .into();

                for (i, f) in fields.into_iter().enumerate() {
                    let exp_ptr = self
                        .gen_expression_code(f, current_block, variable_store)?
                        .unwrap();

                    struct_ptr = current_block
                        .append_operation(llvm::insert_value(
                            &self.context,
                            struct_ptr,
                            DenseI64ArrayAttribute::new(self.context, &[i as i64]),
                            exp_ptr,
                            location,
                        ))
                        .result(0)?
                        .into();
                }
                Some(struct_ptr)
            }

            TypedExpression::Operation(operation) => {
                let typed_ast::Operation::Binary(first_operand, operator, second_operand) =
                    operation.as_ref();

                let first_operand_value = self
                    .gen_expression_code(first_operand.clone(), current_block, variable_store)?
                    .unwrap();

                let second_operand_value = self
                    .gen_expression_code(second_operand.clone(), current_block, variable_store)?
                    .unwrap();

                let operation = match operator {
                    crate::parser::Operator::GreaterThan => arith::cmpi(
                        self.context,
                        arith::CmpiPredicate::Sgt,
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),
                    crate::parser::Operator::GreaterThanOrEqual => arith::cmpi(
                        self.context,
                        arith::CmpiPredicate::Sge,
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),
                    crate::parser::Operator::LessThan => arith::cmpi(
                        self.context,
                        arith::CmpiPredicate::Slt,
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),
                    crate::parser::Operator::LessThanOrEqual => arith::cmpi(
                        self.context,
                        arith::CmpiPredicate::Sle,
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),
                    crate::parser::Operator::Addition => melior::dialect::arith::addi(
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),

                    crate::parser::Operator::Subtraction => melior::dialect::arith::subi(
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),
                    crate::parser::Operator::Multiplication => melior::dialect::arith::muli(
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),
                    crate::parser::Operator::Division => melior::dialect::arith::divsi(
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),
                    crate::parser::Operator::Equality => arith::cmpi(
                        self.context,
                        arith::CmpiPredicate::Eq,
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),
                    crate::parser::Operator::Inequality => arith::cmpi(
                        self.context,
                        arith::CmpiPredicate::Ne,
                        first_operand_value,
                        second_operand_value,
                        location,
                    ),
                };

                let result = current_block.append_operation(operation).result(0)?;
                Some(result.into())
            }

            TypedExpression::Value(TSValue::Boolean(b), _) => {
                let i = if b { 1 } else { 0 };
                Some(
                    current_block
                        .append_operation(melior::dialect::arith::constant(
                            self.context,
                            IntegerAttribute::new(i, IntegerType::new(self.context, 1).into())
                                .into(),
                            location,
                        ))
                        .result(0)?
                        .into(),
                )
            }

            TypedExpression::While(While { condition, block }) => {
                let condition_region = {
                    let block = Block::new(&[]);
                    let mut variables = variable_store.clone();

                    block.append_operation(scf::condition(
                        self.gen_expression_code(*condition, &block, &mut variables)?
                            .unwrap(),
                        &[],
                        location,
                    ));

                    let region = Region::new();
                    region.append_block(block);
                    region
                };

                let operation = scf::r#while(
                    &[],
                    &[],
                    condition_region,
                    self.gen_block(block, variable_store)?.0,
                    location,
                );
                current_block.append_operation(operation);

                None
            }

            TypedExpression::Return(Return { expression }) => {
                let return_values = if let Some(expression) = expression {
                    let return_val = self
                        .gen_expression_code(*expression, current_block, variable_store)?
                        .unwrap();
                    vec![return_val]
                } else {
                    Vec::new()
                };

                current_block
                    .append_operation(melior::dialect::func::r#return(&return_values, location));

                None
            }

            TypedExpression::Array(Array { items, .. }) => {
                let array_len = items.len();
                let item_values = items
                    .into_iter()
                    .map(|item| self.gen_expression_code(item, current_block, variable_store))
                    .collect::<Result<Vec<Option<Value>>>>()?;

                let array_ptr = current_block
                    .append_operation(memref::alloca(
                        self.context,
                        MemRefType::new(
                            item_values[0].unwrap().r#type().into(),
                            &[array_len as i64],
                            None,
                            None,
                        ),
                        &[],
                        &[],
                        None,
                        location,
                    ))
                    .result(0)
                    .unwrap()
                    .into();

                for (index, item) in item_values.into_iter().enumerate() {
                    let item = item.unwrap();
                    let index = current_block
                        .append_operation(melior::dialect::index::constant(
                            self.context,
                            IntegerAttribute::new(
                                index as i64,
                                melior::ir::Type::index(self.context),
                            )
                            .into(),
                            location,
                        ))
                        .result(0)
                        .unwrap();

                    current_block.append_operation(memref::store(
                        item,
                        array_ptr,
                        &[index.into()],
                        location,
                    ));
                }

                Some(array_ptr)
            }

            TypedExpression::ArrayLookup(ArrayLookup {
                array_identifier,
                index_expression,
            }) => {
                let Some(array_ptr) = variable_store.get(&array_identifier) else {
                    bail!("failed to find array {}", array_identifier.0);
                };

                let index = self
                    .gen_expression_code(
                        *index_expression,
                        current_block,
                        &mut variable_store.clone(),
                    )?
                    .unwrap();

                let casted_index = current_block
                    .append_operation(melior::dialect::index::casts(
                        index,
                        melior::ir::Type::index(self.context),
                        location,
                    ))
                    .result(0)
                    .unwrap();

                let gep_op = current_block
                    .append_operation(memref::load(*array_ptr, &[], location))
                    .result(0)
                    .unwrap();

                let gep_op_2 = current_block
                    .append_operation(memref::load(
                        gep_op.into(),
                        &[casted_index.into()],
                        location,
                    ))
                    .result(0)
                    .unwrap();

                Some(gep_op_2.into())
            }

            _ => todo!("code gen uninplemented for {:?}", exp),
        };

        Ok(val)
    }

    pub fn gen_pointer_to_annon_str<'a>(
        &self,
        current_block: &'a Block<'ctx>,
        value: String,
    ) -> Result<OperationRef<'ctx, 'a>> {
        self.generate_annon_string(value, current_block)
    }

    fn generate_annon_string<'a>(
        &self,
        value: String,
        current_block: &'a Block<'ctx>,
    ) -> Result<OperationRef<'ctx, 'a>> {
        let location = melior::ir::Location::unknown(self.context);
        let id = self.gen_annon_string_id();
        let string_type = llvm::r#type::array(
            IntegerType::new(&self.context, 8).into(),
            (value.len()) as u32,
        );
        let op = OperationBuilder::new("llvm.mlir.global", location)
            .add_regions([Region::new()])
            .add_attributes(&[
                (
                    Identifier::new(&self.context, "value"),
                    StringAttribute::new(&self.context, &format!("{value}")).into(),
                ),
                (
                    Identifier::new(&self.context, "sym_name"),
                    StringAttribute::new(&self.context, &id).into(),
                ),
                (
                    Identifier::new(&self.context, "global_type"),
                    TypeAttribute::new(string_type).into(),
                ),
                (
                    Identifier::new(&self.context, "linkage"),
                    // ArrayAttribute::new(&self.context, &[]).into(),
                    llvm::attributes::linkage(&self.context, Linkage::Internal),
                ),
            ])
            .build()?;

        self.module.body().append_operation(op);

        let address_op = OperationBuilder::new("llvm.mlir.addressof", location)
            // .enable_result_type_inference()
            .add_attributes(&[(
                Identifier::new(&self.context, "global_name"),
                FlatSymbolRefAttribute::new(&self.context, &id).into(),
            )])
            .add_results(&[llvm::r#type::opaque_pointer(&self.context)])
            .build()?;

        Ok(current_block.append_operation(address_op))
    }
}

pub fn generate_mlir<'c>(ast: TypedProgram, emit_mlir: bool) -> Result<ExecutionEngine> {
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);

    let context = Context::new();
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
    register_all_llvm_translations(&context);

    context.attach_diagnostic_handler(|diagnostic| {
        eprintln!("{}", diagnostic);
        true
    });

    let mut module = Module::new(melior::ir::Location::unknown(&context));
    let code_gen = Box::new(CodeGen::new(
        &context,
        &module,
        ast.types.clone(),
        ast.variable_types.clone(),
    ));
    let code_gen = Box::leak(code_gen);

    code_gen.gen_ast_code(ast, emit_mlir)?;

    let pass_manager = pass::PassManager::new(&code_gen.context);
    pass_manager.add_pass(pass::conversion::create_func_to_llvm());

    pass_manager
        .nested_under("func.func")
        .add_pass(pass::conversion::create_arith_to_llvm());
    pass_manager
        .nested_under("func.func")
        .add_pass(pass::conversion::create_index_to_llvm());
    pass_manager.add_pass(pass::conversion::create_scf_to_control_flow());
    pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    pass_manager.add_pass(pass::conversion::create_finalize_mem_ref_to_llvm());
    pass_manager.add_pass(pass::conversion::create_index_to_llvm());
    pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());

    pass_manager.run(&mut module)?;

    if !emit_mlir {
        assert!(module.as_operation().verify());
    }

    if emit_mlir {
        println!("{}", module.as_operation());
    }

    let engine = ExecutionEngine::new(&module, 0, &[], true);

    Ok(engine)
}
