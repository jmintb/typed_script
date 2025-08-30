use anyhow::bail;
use anyhow::Result;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::parser::AccessModes;
use crate::parser::TSIdentifier;
use crate::parser::TSValue;

use crate::typed_ast::Decl;
use crate::typed_ast::Type;
use crate::typed_ast::TypedAst;

use crate::typed_ast::TypedProgram;

pub struct ModuleID(usize);

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct TypeID(usize);

impl From<usize> for TypeID {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl Into<usize> for TypeID {
    fn into(self) -> usize {
        self.0
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct FunctionID(usize);
impl From<usize> for FunctionID {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl Into<usize> for FunctionID {
    fn into(self) -> usize {
        self.0
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct VariableID(usize);
impl From<usize> for VariableID {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl Into<usize> for VariableID {
    fn into(self) -> usize {
        self.0
    }
}
#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct ScopeID(usize);

pub struct Module {
    modules: Vec<ModuleID>,
    name: String,
    types: Vec<TypeID>,
    functions: Vec<FunctionID>,
}

impl Module {
    pub fn new(name: String) -> Self {
        Self {
            modules: Vec::new(),
            name,
            types: Vec::new(),
            functions: Vec::new(),
        }
    }
}

pub struct Scope {
    variables: BTreeSet<VariableID>,
    parent_scope: Option<ScopeID>,
    function_id: FunctionID,
}

impl Scope {
    fn new(function_id: FunctionID) -> Self {
        Self {
            variables: BTreeSet::new(),
            function_id,
            parent_scope: None,
        }
    }

    fn from_parent(parent_id: ScopeID, scopes: &BTreeMap<ScopeID, Scope>) -> Self {
        let mut child = Self::new(scopes.get(&parent_id).unwrap().function_id);
        child.parent_scope = Some(parent_id);
        child
    }

    fn declare_variable(&mut self, variable_id: VariableID) -> Result<()> {
        let existing_variable = !self.variables.insert(variable_id);

        if existing_variable {
            bail!(format!(
                "the variable with ID {} was already delclared",
                variable_id.0
            ));
        }

        Ok(())
    }
}

pub struct ScopedProgram {
    modules: BTreeMap<ModuleID, Module>,
    types: BTreeMap<TypeID, Type>,
    functions: BTreeMap<FunctionID, Decl>,
    variables: BTreeMap<VariableID, TSValue>,
    entry_module: ModuleID,
}

pub struct ScopedProgramBuilder {
    modules: BTreeMap<ModuleID, Module>,
    types: BTreeMap<TypeID, Type>,
    functions: BTreeMap<FunctionID, Decl>,
    variables: BTreeMap<VariableID, (TSValue, Type, AccessModes)>,
    names: BTreeMap<usize, TSIdentifier>,
    ids: BTreeMap<TSIdentifier, usize>,
    entry_module: Option<ModuleID>,
    id_counter: usize,
    scopes: BTreeMap<ScopeID, Scope>,
}

impl ScopedProgramBuilder {
    fn new_id<T: From<usize> + Copy>(&mut self) -> T {
        let new_id = self.id_counter;
        self.id_counter += 1;
        T::from(new_id)
    }

    fn new_id_for_name<T: From<usize> + Into<usize> + Copy>(&mut self, name: TSIdentifier) -> T {
        let id = self.new_id::<T>();
        self.names.insert(id.into(), name.clone());
        self.ids.insert(name, id.into());
        id
    }

    fn store_type(&mut self, name: TSIdentifier, r#type: Type) -> TypeID {
        let id = self.new_id_for_name::<TypeID>(name);
        self.types.insert(id, r#type);
        id
    }

    fn new() -> Self {
        Self {
            modules: BTreeMap::new(),
            types: BTreeMap::new(),
            functions: BTreeMap::new(),
            variables: BTreeMap::new(),
            entry_module: None,
            names: BTreeMap::new(),
            ids: BTreeMap::new(),
            id_counter: 0,
            scopes: BTreeMap::new(),
        }
    }

    fn build(self) -> Result<ScopedProgram> {
        todo!()
    }

    pub fn generate_scoped_progam(typed_modules: Vec<TypedProgram>) -> Result<ScopedProgram> {
        let mut builder = Self::new();

        for typed_module in typed_modules {
            let _module = Module::new("main".to_string());
            for r#type in typed_module.types {
                builder.store_type(r#type.0, r#type.1);
            }

            for entry in typed_module.ast {
                match entry {
                    TypedAst::Decl(f @ Decl::Function { .. }) => {
                        let function_id = builder.store_function(f);
                        let scope_id = builder.new_scope(function_id);

                        builder.scope_function(function_id, scope_id)?;
                    }
                    _ => todo!(),
                }
            }
        }

        builder.build()
    }

    fn store_function(&mut self, f: Decl) -> FunctionID {
        let Decl::Function { ref id, .. } = f else {
            todo!()
        };
        let id = self.new_id_for_name(id.clone());
        self.functions.insert(id, f);
        id
    }

    fn new_scope(&self, _function_id: FunctionID) -> ScopeID {
        todo!()
    }

    fn scope_function(&mut self, function_id: FunctionID, scope_id: ScopeID) -> Result<()> {
        // NEXT: each block is really interested in the parent scope and building the current scope;
        let Decl::Function {
            keywords: _,
            id: _,
            arguments,
            body,
            return_type: _,
        } = self.functions.get(&function_id).cloned().unwrap()
        else {
            todo!()
        };

        for argument in arguments.clone() {
            let variable_id =
                self.store_variable(argument.name, argument.r#type, argument.access_mode);
            let scope = self.scopes.get_mut(&scope_id).unwrap();
            scope.declare_variable(variable_id)?;
        }

        for _node in body {
            // match node {
            //     TypedAst::Expression(TypedExpression::Assign(Assign { id, expression })) => {
            //         self.store_variable(id, expression.r#type(&BTreeMap::new())?, AccessModes::Let);
            //     }
            // }
        }

        Ok(())
    }

    fn store_variable(
        &mut self,
        name: TSIdentifier,
        r#type: Type,
        access_mode: crate::parser::AccessModes,
    ) -> VariableID {
        let id = self.new_id_for_name(name.clone());
        self.variables
            .insert(id, (TSValue::Variable(name.clone()), r#type, access_mode));
        self.ids.insert(name, id.0);
        id
    }
}

struct ScopedFunction {}
