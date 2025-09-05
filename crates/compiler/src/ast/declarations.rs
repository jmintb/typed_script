use super::{
    identifiers::{DeclarationID, FunctionDeclarationID, StructDeclarationID},
    nodes::Identifier,
};

#[derive(Default, Clone, Debug)]
pub struct ModuleDeclaration {
    pub struct_declarations: Vec<StructDeclarationID>,
    pub function_declarations: Vec<FunctionDeclarationID>,
    pub identifier: Identifier,
}

impl ModuleDeclaration {
    pub fn new(identifier: Identifier) -> Self {
        Self {
            struct_declarations: Vec::new(),
            function_declarations: Vec::new(),
            identifier,
        }
    }

    pub fn declare(&mut self, id: DeclarationID) {
        // TODO: collisions?
        match id {
            DeclarationID::StructDeclaration(id) => {
                self.struct_declarations.push(id);
            }
            DeclarationID::FunctionDeclaration(id) => {
                self.function_declarations.push(id);
            }
            DeclarationID::ModuleDeclarationID(_id) => todo!(),
        }
    }
}
