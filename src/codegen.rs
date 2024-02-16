use std::{cell::RefCell, collections::HashMap, ops::Index};

use anyhow::{bail, Result};
use clap::builder;
use melior::{
    dialect::{
        arith,
        func::{self, call},
        llvm::{self, attributes::Linkage, r#type::function, AllocaOptions, LoadStoreOptions},
        memref, scf, DialectRegistry,
    },
    ir::{
        attribute::{
            ArrayAttribute, DenseI32ArrayAttribute, FlatSymbolRefAttribute, IntegerAttribute,
            StringAttribute, TypeAttribute,
        },
        operation::{OperationBuilder, OperationResult},
        r#type::{FunctionType, IntegerType},
        Attribute, AttributeLike, Block, BlockRef, Identifier, Location, Module, Operation,
        OperationRef, Region, Type, Value,
    },
    pass,
    utility::{register_all_dialects, register_all_llvm_translations, register_all_passes},
    Context, ExecutionEngine,
};

use crate::{
    parser::{Ast, FunctionKeyword, TSExpression, TSIdentifier, TSValue},
    typed_ast::{
        self, Assignment, Decl, FunctionArg, IfStatement, TypedAst, TypedExpression, TypedProgram,
    },
};

// TODO: something inside the module is dropped when it is returned.
// That is why we return the exection engine at the moment.

/// Creates a `llvm.getelementptr` operation.
pub fn get_element_ptr_typed<'c>(
    context: &'c Context,
    ptr: Value<'c, '_>,
    indices: DenseI32ArrayAttribute<'c>,
    result_type: Type<'c>,
    location: Location<'c>,
) -> Operation<'c> {
    OperationBuilder::new("llvm.getelementptr", location)
        .add_attributes(&[(
            Identifier::new(context, "rawConstantIndices"),
            indices.into(),
        )])
        .add_operands(&[ptr])
        .add_results(&[result_type])
        .build()
}

struct CodeGen<'ctx, 'module> {
    context: &'ctx Context,
    module: &'module Module<'ctx>,
    annon_string_counter: RefCell<usize>,
    llvm_type_store: HashMap<TSIdentifier, Type<'ctx>>,
    type_store: HashMap<TSIdentifier, typed_ast::Type>,
    var_to_type: HashMap<TSIdentifier, typed_ast::Type>,
}

impl<'ctx, 'module> CodeGen<'ctx, 'module> {
    fn new(
        context: &'ctx Context,
        module: &'module Module<'ctx>,
        types: HashMap<TSIdentifier, typed_ast::Type>,
        variable_types: HashMap<TSIdentifier, typed_ast::Type>,
    ) -> Self {
        Self {
            context,
            module,
            annon_string_counter: 0.into(),
            llvm_type_store: HashMap::new(),
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

    fn gen_declaration<'a>(&'a self, decl: Decl, location: Location<'a>) -> Result<Operation>
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
            panic!("recived a non function declaration");
        };

        let argument_types = arguments
            .iter()
            .map(|arg_type| arg_type.r#type.as_mlir_type(self.context))
            .collect::<Vec<Type<'ctx>>>();
        let mlir_return_type = return_type.as_mlir_type(self.context);

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
            variable_store.insert(
                argument.name.clone(),
                function_block
                    .argument(position)
                    .expect(&format!(
                        "expected at least {} function arguments for fn: {}",
                        position, id.0,
                    ))
                    .into(),
            );
        }

        // for exp in body.unwrap_or(vec![]) {
        //     match exp.clone() {
        //         TypedAst::Expression(exp) => {
        if let Some(body) = body {
            self.gen_statements(body, &function_block, &mut variable_store, true)?;
            function_region.append_block(function_block);
        }
        // }
        // TypedAst::Expression(TypedExpression::Call(id, args)) => {
        //     let actual_args: Vec<Value> = args
        //         .iter()
        //         .map(|arg| match arg {
        //             TypedExpression::Value(TSValue::String(ref val), Type) => {
        //                 // TODO: \n is getting escaped, perhap we need a raw string?
        //                 let val = if val == "\\n" { "\n" } else { val };

        //                 let ptr_op = self
        //                     .gen_pointer_to_annon_str(
        //                         location.clone(),
        //                         val.to_string(),
        //                         &module,
        //                     )
        //                     .unwrap();

        //                 function_block
        //                     .append_operation(ptr_op)
        //                     .result(0)
        //                     .unwrap()
        //                     .into()
        //             }
        //             TypedExpression::Value(TSValue::Variable(ref id), Type) => {
        //                 if let Some(v) = variable_store.get(id) {
        //                     v.to_owned().into()
        //                 } else {
        //                     function_block
        //                         .argument(
        //                             arguments
        //                                 .iter()
        //                                 .position(|farg| &farg.name == id)
        //                                 .ok_or(format!(
        //                                     "failed to match argument: {:?} {id:?} {:?}",
        //                                     arguments
        //                                         .iter()
        //                                         .map(|farg| farg.name.clone())
        //                                         .collect::<Vec<TSIdentifier>>(),
        //                                     variable_store
        //                                 ))
        //                                 .unwrap(),
        //                         )
        //                         .unwrap()
        //                         .into()
        //                 }
        //             }
        //             TypedExpression::Value(TSValue::Integer(v), _) => {
        //                 // next
        //                 let const_op = melior::dialect::arith::constant(
        //                     &self.context,
        //                     IntegerAttribute::new(
        //                         *v as i64,
        //                         IntegerType::new(&self.context, 32).into(),
        //                     )
        //                     .into(),
        //                     location,
        //                 );

        //                 function_block
        //                     .append_operation(const_op)
        //                     .result(0)
        //                     .unwrap()
        //                     .into()
        //             }
        //             e => todo!("not yet implemented: {:?}", e),
        //         })
        //         .collect();

        //     let fn_type = self.type_store.get(&id).unwrap();

        //     let (callee_keywords, return_type) =
        //         if let typed_ast::Type::Function(keywords, _, return_type) = fn_type {
        //             (keywords, return_type)
        //         } else {
        //             panic!(
        //                 "failed to find a function dcelaration or return type for {}",
        //                 id.0
        //             );
        //         };

        //     if callee_keywords.contains(&FunctionKeyword::LlvmExtern) {
        //         let op = OperationBuilder::new("llvm.call", location)
        //             .add_operands(&actual_args)
        //             .add_attributes(&[(
        //                 Identifier::new(&self.context, "callee"),
        //                 FlatSymbolRefAttribute::new(&self.context, &id.0).into(),
        //             )]);

        //         function_block.append_operation(match **return_type {
        //             typed_ast::Type::Unit => op.build(),
        //             _ => op
        //                 .add_results(&[return_type.as_mlir_type(&self.context)])
        //                 .build(),
        //         });
        //     } else {
        //         let res = function_block.append_operation(func::call(
        //             &self.context,
        //             FlatSymbolRefAttribute::new(&self.context, &id.0),
        //             &actual_args,
        //             &[],
        //             location,
        //         ));
        //     }

        // let call = llvm::ca(
        //     &self.context,
        //     FlatSymbolRefAttribute::new(&self.context, "printf"),
        //     &[op.result(0).unwrap().into()],
        //     &[Type::none(&self.context)],
        //     location,
        // );

        // block.append_operation(func::r#return(&[], location));
        // }
        // TypedAst::Expression(TypedExpression::Struct(id, fields)) => {
        //     let size = melior::dialect::arith::constant(
        //         &self.context,
        //         IntegerAttribute::new(
        //             4, // TODO why do we need 4 here?
        //             IntegerType::new(&self.context, 32).into(),
        //         )
        //         .into(),
        //         location,
        //     );
        //     let res = function_block.append_operation(size);
        //     let ptr_type = if let Some(ty) = self.type_store.get(&id).cloned() {
        //         llvm::r#type::pointer(ty.as_mlir_type(self.context), 0)
        //     } else {
        //         bail!("Could not find a type for ID: {id:?}")
        //     };

        //     let empty_struct = llvm::alloca(
        //         &self.context,
        //         res.result(0).unwrap().into(),
        //         ptr_type,
        //         location,
        //         AllocaOptions::new(),
        //     );

        //     let struct_ptr = function_block.append_operation(empty_struct).result(0)?;

        //     let string_type =
        //         llvm::r#type::array(IntegerType::new(&self.context, 8).into(), 2 as u32);

        //     let string_ptr = llvm::r#type::pointer(string_type, 0);

        //     let ele_type = llvm::r#type::r#struct(
        //         self.context,
        //         &[string_type.clone(), string_type],
        //         false,
        //     );

        //     for (i, f) in fields.into_iter().enumerate() {
        //         let field_ptr_op = llvm::get_element_ptr(
        //             &self.context,
        //             struct_ptr.into(),
        //             DenseI32ArrayAttribute::new(&self.context, &[0, i as i32]),
        //             ele_type,
        //             llvm::r#type::opaque_pointer(&self.context),
        //             location,
        //         );

        //         let field_ptr = function_block.append_operation(field_ptr_op).result(0)?;

        //         let exp_ptr_op =
        //             self.gen_expression_code(f, location, &module, &variable_store)?;

        //         let exp_ptr = exp_ptr_op
        //             .into_iter()
        //             .map(|operation| {
        //                 function_block
        //                     .append_operation(operation)
        //                     .result(0)
        //                     .unwrap()
        //             })
        //             .last()
        //             .unwrap();

        //         let store_op = llvm::store(
        //             &self.context,
        //             exp_ptr.into(),
        //             field_ptr.into(),
        //             location,
        //             LoadStoreOptions::new(),
        //         );

        //         function_block.append_operation(store_op);
        //     }
        // }

        // TypedAst::Assignment(id, exp, type_anno) => {
        //     // if let TypedExpression::Struct(type_id, _) = exp.clone() {
        //     //     self.var_to_type.insert(id.clone(), type_id);
        //     // }

        //     let exp_op =
        //         self.gen_expression_code(exp, location, &module, &variable_store)?;

        //     println!("test {:?}", exp_op);

        //     let result = exp_op
        //         .into_iter()
        //         .map(|operation| function_block.append_operation(operation))
        //         .last()
        //         .map(|operation| operation.result(0).unwrap());

        //     if let Some(exp_result) = result {
        //         variable_store.insert(id, exp_result);
        //     }
        //     println!("assignment");
        // }

        //         e => todo!("not yet ready for {:?}", e),
        //     }
        // }

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
                        return_type.as_mlir_type(&self.context),
                        arguments
                            .iter()
                            .map(|a| a.r#type.as_mlir_type(&self.context))
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
                TypeAttribute::new(FunctionType::new(&self.context, &argument_types, &[]).into()),
                function_region,
                &[],
                location,
            )
        };

        Ok(functiom_decl)
    }

    fn gen_ast_code(&'ctx self, ast: TypedProgram, emit_mlir: bool) -> Result<()> {
        let location = Location::unknown(&self.context);

        for node in ast.ast {
            let mut variable_store: HashMap<TSIdentifier, OperationResult> = HashMap::new();
            match node.clone() {
                TypedAst::Decl(
                    ref d @ Decl::Function {
                        ref id,
                        ref arguments,
                        ref body,
                        ref return_type,
                        ..
                    },
                ) => {
                    let function_decl = self.gen_declaration(d.clone(), location)?;

                    self.module.body().append_operation(function_decl);
                }
                TypedAst::Decl(Decl::Struct(..)) => {}
                _ => todo!(),
            }
        }

        Ok(())
    }

    fn gen_struct_expression_block<'a, 'c>(
        &'a self,
        exp: TypedExpression,
        location: Location<'a>,
        llvm_value_store: HashMap<TSIdentifier, OperationResult<'a, 'a>>,
        function_block: &'a Block,
    ) -> Result<()>
    where
        'a: 'c,
    {
        let res = match exp {
            e => todo!("unimplemented: {e:?}"),
        };

        Ok(res)
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

        let res = self.gen_statements(block.statements, &builder, &mut variable_store, false);

        let mut region = Region::new();
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
        let mut return_value: Option<Value> = None;

        for node in nodes {
            match node {
                TypedAst::Expression(exp) => {
                    let val = self.gen_expression_code(exp, current_block, variable_store)?;
                    return_value = val;
                }
                TypedAst::Decl(decl) => {
                    todo!("we do not support declarations inside functions yet");
                }
                TypedAst::Assignment(assignment) => {
                    self.gen_assignment_code(assignment, current_block, variable_store)?;
                }
            }
        }

        // if let Some(return_value) = return_value {
        //     current_block.append_operation(func::r#return(&[return_value], location));
        // } else {
        if function_scope {
            current_block.append_operation(func::r#return(&[], location));
        } else {
            current_block.append_operation(scf::r#yield(&[], location));
        }
        // }

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
            variable_store.insert(assignment.id, initial_value);
        } else {
            bail!(format!(
                "assingment expression did not return a value: {:#?} {:#?}",
                assignment,
                self.type_store.get(&TSIdentifier("fdopen".to_string()))
            ));
        }

        Ok(())
    }

    fn gen_expression_code<'a>(
        &self,
        exp: TypedExpression,
        current_block: &'a Block<'ctx>,
        variable_store: &mut HashMap<TSIdentifier, Value<'ctx, 'a>>,
    ) -> Result<Option<Value<'ctx, 'a>>> {
        let location = melior::ir::Location::unknown(self.context);
        let val: Option<Value> = match exp {
            TypedExpression::Value(TSValue::String(val), vtype) => {
                // TODO: \n is getting escaped, perhap we need a raw string?
                let val = if val == "\\n" { "\n" } else { &val };
                let val = val.replace("\\n", "\n");

                Some(
                    self.gen_pointer_to_annon_str(current_block, val.to_string())?
                        .result(0)?
                        .into(),
                )
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
            TypedExpression::Value(TSValue::Variable(ref id), Type) => {
                if let Some(v) = variable_store.get(id) {
                    Some(v.clone())
                } else {
                    bail!("Failed to find variable {}", id.0)
                }
            }
            TypedExpression::StructFieldRef(..) => todo!(),
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
                    OperationBuilder::new("llvm.call", location)
                        .add_operands(&actual_args)
                        .add_attributes(&[(
                            Identifier::new(&self.context, "callee"),
                            FlatSymbolRefAttribute::new(&self.context, &id.0).into(),
                        )])
                        .add_results(&[return_type.as_mlir_type(self.context)])
                        .build()
                } else {
                    func::call(
                        &self.context,
                        FlatSymbolRefAttribute::new(&self.context, &id.0),
                        &actual_args,
                        &[],
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

                let Some(field_index) = (if let typed_ast::Type::Struct(fields) = struct_type {
                    fields.iter().position(|f| f.0 == field_id)
                } else {
                    bail!(
                        "Expected to find a struct type for variable {} instead found {:#?}",
                        struct_id.0,
                        struct_type
                    );
                }) else {
                    bail!(
                        "Failed to find field {} in struct {:?}",
                        field_id.0,
                        struct_type
                    );
                };

                let gep = llvm::get_element_ptr(
                    self.context,
                    struct_ptr.into(),
                    DenseI32ArrayAttribute::new(self.context, &[0, field_index as i32]),
                    struct_type.as_mlir_type(&self.context).to_owned(),
                    llvm::r#type::opaque_pointer(self.context),
                    location,
                );
                let gep_ref: Value = current_block.append_operation(gep).result(0)?.into();

                let v = llvm::load(
                    &self.context,
                    gep_ref.into(),
                    llvm::r#type::opaque_pointer(self.context),
                    location,
                    LoadStoreOptions::new(),
                );

                current_block.append_operation(v);
                Some(gep_ref)
            }
            TypedExpression::Struct(id, fields) => {
                let size = melior::dialect::arith::constant(
                    &self.context,
                    IntegerAttribute::new(1, IntegerType::new(&self.context, 32).into()).into(),
                    location,
                );

                let res = size
                    .result(0)
                    .expect("expected arith operation to produce a result");

                let ptr_type = if let Some(ty) = self.type_store.get(&id).cloned() {
                    llvm::r#type::pointer(ty.as_mlir_type(self.context), 0)
                } else {
                    bail!("Could not find an LLVM type for ID: {id:?}");
                };

                // TODO: this should be fixed lenth
                let str_type = |val: String| {
                    llvm::r#type::array(IntegerType::new(&self.context, 8).into(), val.len() as u32)
                };

                let str_ptr_type = |val: String| llvm::r#type::pointer(str_type(val), 0);

                let exp_ptr = |exp: TypedExpression| match exp {
                    TypedExpression::Value(TSValue::String(val), etype) => str_ptr_type(val),
                    _ => todo!("missing implementation"),
                };

                let struct_type = llvm::r#type::r#struct(
                    self.context,
                    fields
                        .clone()
                        .into_iter()
                        .map(exp_ptr)
                        .collect::<Vec<Type>>()
                        .as_slice(),
                    true,
                );

                let struct_ptr: Value = current_block
                    .append_operation(llvm::alloca(
                        &self.context,
                        res.into(),
                        ptr_type,
                        location,
                        AllocaOptions::new(),
                    ))
                    .result(0)?
                    .into();

                for (i, f) in fields.into_iter().enumerate() {
                    let field_ptr = current_block
                        .append_operation(llvm::get_element_ptr(
                            &self.context,
                            struct_ptr,
                            DenseI32ArrayAttribute::new(&self.context, &[0, i as i32]),
                            struct_type,
                            llvm::r#type::opaque_pointer(&self.context),
                            location,
                        ))
                        .result(0)?
                        .into();

                    let mut exp_ptr = self
                        .gen_expression_code(f, current_block, variable_store)?
                        .unwrap();

                    let store_op = llvm::store(
                        &self.context,
                        exp_ptr.into(),
                        field_ptr,
                        location,
                        LoadStoreOptions::new(),
                    );
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

            _ => todo!("code gen uninplemented for {:?}", exp),
        };

        Ok(val)
    }

    pub fn gen_pointer_to_annon_str<'a>(
        &self,
        current_block: &'a Block<'ctx>,
        value: String,
    ) -> Result<OperationRef<'ctx, 'a>> {
        let location = melior::ir::Location::unknown(self.context);
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
            .add_regions(vec![Region::new()])
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
            .build();

        self.module.body().append_operation(op);

        let address_op = OperationBuilder::new("llvm.mlir.addressof", location)
            // .enable_result_type_inference()
            .add_attributes(&[(
                Identifier::new(&self.context, "global_name"),
                FlatSymbolRefAttribute::new(&self.context, &id).into(),
            )])
            .add_results(&[llvm::r#type::opaque_pointer(&self.context)])
            .build();

        Ok(current_block.append_operation(address_op))
    }
}

pub fn generate_mlir<'c>(ast: TypedProgram, emit_mlir: bool) -> Result<ExecutionEngine> {
    let context = Context::new();
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

    // register_all_dialects(&registry);
    // context.append_dialect_registry(&registry);
    // context.get_or_load_dialect("func");
    // context.get_or_load_dialect("arith");
    // context.get_or_load_dialect("llvm");
    // context.get_or_load_dialect("scf");
    // context.get_or_load_dialect("cf");
    let mut module = Module::new(melior::ir::Location::unknown(&context));
    // register_all_llvm_translations(&context);
    let code_gen = Box::new(CodeGen::new(
        &context,
        &module,
        ast.types.clone(),
        ast.variable_types.clone(),
    ));
    let code_gen = Box::leak(code_gen);

    code_gen.gen_ast_code(ast, emit_mlir)?;
    if !emit_mlir {
        assert!(module.as_operation().verify());
    }

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

    // register_all_passes();
    // pass_manager.enable_verifier(true);
    // pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_scf_to_control_flow());

    // pass_manager.add_pass(pass::conversion::create_index_to_llvm_pass());
    // pass_manager.add_pass(pass::conversion::create_mem_ref_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());
    // pass::conversion::register_func_to_llvm();

    // pass_manager.enable_ir_printing();

    // pass_manager
    //     .nested_under("func.func")
    //     .add_pass(pass::conversion::create_arith_to_llvm());

    pass_manager.run(&mut module);

    if emit_mlir {
        println!("{}", module.as_operation());
    }

    let engine = ExecutionEngine::new(&module, 0, &[], true);

    Ok(engine)

    // for node in ast.0 {
    //     match node {
    //         TypedAst::Function(id, fargs, body) => {
    //             let region = Region::new();
    //             let function_block = Block::new(
    //                 fargs
    //                     .iter()
    //                     .map(|_| (llvm::r#type::opaque_pointer(&context), location))
    //                     .collect::<Vec<(Type, Location)>>()
    //                     .as_slice(),
    //             );

    //             let function_block = region.append_block(function_block);

    //             for exp in body {
    //                 match exp.clone() {
    //                     TypedAst::Expression(TSExpression::Call(id, args)) => {
    //                         let exp_block = function_block;
    //                         let actual_args: Vec<Value> = args
    //                             .iter()
    //                             .map(|arg| match arg {
    //                                 TSExpression::Value(TSValue::String(ref val)) => {
    //                                     // TODO: \n is getting escaped, perhap we need a raw string?
    //                                     let val = if val == "\\n" { "\n" } else { val };

    //                                     gen_pointer_to_annon_str(
    //                                         &context,
    //                                         &mut gen_annon_string,
    //                                         &exp_block,
    //                                         location.clone(),
    //                                         val.to_string(),
    //                                         &mut module,
    //                                     )
    //                                     .unwrap()
    //                                     .into()
    //                                 }
    //                                 TSExpression::Value(TSValue::Variable(ref id)) => exp_block
    //                                     .argument(
    //                                         fargs
    //                                             .iter()
    //                                             .position(|farg| &farg.0 == id)
    //                                             .ok_or(format!(
    //                                                 "failed to match argument: {:?} {id}",
    //                                                 fargs
    //                                                     .iter()
    //                                                     .map(|farg| farg.clone())
    //                                                     .collect::<Vec<TSIdentifier>>()
    //                                             ))
    //                                             .unwrap(),
    //                                     )
    //                                     .unwrap()
    //                                     .into(),
    //                                 _ => todo!(),
    //                             })
    //                             .collect();

    //                         let res = exp_block.append_operation(
    //                             OperationBuilder::new("llvm.call", location)
    //                                 .add_operands(&actual_args)
    //                                 .add_attributes(&[(
    //                                     Identifier::new(&context, "callee"),
    //                                     FlatSymbolRefAttribute::new(&context, "printf").into(),
    //                                 )])
    //                                 .add_results(&[IntegerType::new(&context, 32).into()])
    //                                 .build(),
    //                         );

    //                         // let call = llvm::ca(
    //                         //     &context,
    //                         //     FlatSymbolRefAttribute::new(&context, "printf"),
    //                         //     &[op.result(0).unwrap().into()],
    //                         //     &[Type::none(&context)],
    //                         //     location,
    //                         // );

    //                         // block.append_operation(func::r#return(&[], location));
    //                     }
    //                     TypedAst::Expression(TSExpression::Struct(id, fields)) => {
    //                         let size = melior::dialect::arith::constant(
    //                             &context,
    //                             IntegerAttribute::new(0, IntegerType::new(&context, 0).into())
    //                                 .into(),
    //                             location,
    //                         );
    //                         let res = function_block.append_operation(size);
    //                         let ptr_type = llvm::r#type::pointer(*llvm_types.get(&id).unwrap(), 0);
    //                         let empty_struct = llvm::alloca(
    //                             &context,
    //                             res.result(0).unwrap().into(),
    //                             ptr_type,
    //                             location,
    //                             AllocaOptions::new(),
    //                         );

    //                         let struct_ptr =
    //                             function_block.append_operation(empty_struct).result(0)?;

    //                         for (i, f) in fields.into_iter().enumerate() {
    //                             let field_ptr_op = llvm::get_element_ptr(
    //                                 &context,
    //                                 struct_ptr.into(),
    //                                 DenseI32ArrayAttribute::new(&context, &[0, i as i32]),
    //                                 llvm::r#type::opaque_pointer(&context),
    //                                 llvm::r#type::opaque_pointer(&context),
    //                                 location,
    //                             );

    //                             let field_ptr =
    //                                 function_block.append_operation(field_ptr_op).result(0)?;
    //                         }
    //                     }
    //                     e => todo!("not yet ready for {:?}", e),
    //                 }
    //             }
    //             function_block.append_operation(llvm::r#return(None, location));

    //             let function = func::func(
    //                 &context,
    //                 StringAttribute::new(&context, &id.0),
    //                 TypeAttribute::new(
    //                     FunctionType::new(
    //                         &context,
    //                         fargs
    //                             .iter()
    //                             .map(|_| llvm::r#type::opaque_pointer(&context).into())
    //                             .collect::<Vec<Type>>()
    //                             .as_slice(),
    //                         &[],
    //                     )
    //                     .into(),
    //                 ),
    //                 region,
    //                 &[(
    //                     Identifier::new(&context, "llvm.emit_c_interface"),
    //                     Attribute::unit(&context),
    //                 )],
    //                 location,
    //             );

    //             module.body().append_operation(function);
    //         }
    //         TypedAst::StructType(id, fields) => {
    //             let struct_ty = llvm::r#type::r#struct(
    //                 &context,
    //                 fields
    //                     .into_iter()
    //                     .map(|f| llvm::r#type::opaque_pointer(&context))
    //                     .collect::<Vec<Type>>()
    //                     .as_slice(),
    //                 true,
    //             );

    //             llvm_types.insert(id, struct_ty);
    //         }
    //         _ => todo!(),
    //     }
    // }

    // assert!(module.as_operation().verify());

    // let pass_manager = pass::PassManager::new(&code_gen.context);
    // register_all_passes();
    // pass_manager.enable_verifier(true);
    // pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_index_to_llvm_pass());
    // pass_manager.add_pass(pass::conversion::create_mem_ref_to_llvm());
    // pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());

    // // pass_manager.enable_ir_printing();

    // pass_manager
    //     .nested_under("func.func")
    //     .add_pass(pass::conversion::create_arith_to_llvm());
    // pass_manager.run(&mut module).unwrap();

    // if emit_mlir {
    //     println!("{}", module.as_operation());
    // }

    // let engine = ExecutionEngine::new(&module, 0, &[], true);

    // Ok(engine)
}
