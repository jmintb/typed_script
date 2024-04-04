use crate::identifiers::ID;

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub struct ModuleDeclarationID(ID);

impl From<ModuleDeclarationID> for NodeID {
    fn from(value: ModuleDeclarationID) -> Self {
        Self::Declaration(DeclarationID::ModuleDeclarationID(value))
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub struct StructDeclarationID(pub ID);

impl From<StructDeclarationID> for NodeID {
    fn from(value: StructDeclarationID) -> Self {
        Self::Declaration(DeclarationID::StructDeclaration(value))
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub struct FunctionDeclarationID(ID);

impl From<ID> for FunctionDeclarationID {
    fn from(value: ID) -> Self {
        Self(value)
    }
}

impl From<FunctionDeclarationID> for NodeID {
    fn from(value: FunctionDeclarationID) -> Self {
        Self::Declaration(DeclarationID::FunctionDeclaration(value))
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub struct ExpressionID(ID);

impl From<ID> for ExpressionID {
    fn from(value: ID) -> Self {
        Self(value)
    }
}

impl From<ExpressionID> for NodeID {
    fn from(value: ExpressionID) -> Self {
        Self::Statement(StatementID::Expression(value))
    }
}

impl From<ExpressionID> for StatementID {
    fn from(value: ExpressionID) -> Self {
        Self::Expression(value)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub struct BlockID(ID);

impl From<usize> for BlockID {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl From<BlockID> for NodeID {
    fn from(value: BlockID) -> Self {
        Self::Block(value)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug, Hash)]
pub enum StatementID {
    Declaration(DeclarationID),
    Expression(ExpressionID),
}

impl From<FunctionDeclarationID> for StatementID {
    fn from(value: FunctionDeclarationID) -> Self {
        StatementID::Declaration(DeclarationID::FunctionDeclaration(value))
    }
}

impl From<StructDeclarationID> for StatementID {
    fn from(value: StructDeclarationID) -> Self {
        StatementID::Declaration(DeclarationID::StructDeclaration(value))
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub enum NodeID {
    Declaration(DeclarationID),
    Block(BlockID),
    Statement(StatementID),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Hash, Debug)]
pub enum DeclarationID {
    StructDeclaration(StructDeclarationID),
    FunctionDeclaration(FunctionDeclarationID),
    ModuleDeclarationID(ModuleDeclarationID),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone)]
pub struct TypeID(usize);

impl From<usize> for TypeID {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl Into<usize> for StructDeclarationID {
    fn into(self) -> usize {
        self.0
    }
}

impl Into<usize> for ModuleDeclarationID {
    fn into(self) -> usize {
        self.0
    }
}

impl From<usize> for StructDeclarationID {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl From<usize> for ModuleDeclarationID {
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
