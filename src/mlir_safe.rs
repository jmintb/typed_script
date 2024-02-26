use std::collections::BTreeMap;

use clap::error::ContextKind;
use melior::{
    ir::{block, Block, Location, Module, Operation, Region, Type},
    Context,
};

#[derive(Copy, Clone, Debug, Ord, Eq, PartialEq, PartialOrd)]
pub struct BlockId(usize);
#[derive(Copy, Clone, Debug, Ord, Eq, PartialEq, PartialOrd)]
pub struct ModuleId(usize);
#[derive(Copy, Clone, Debug, Ord, Eq, PartialEq, PartialOrd)]
pub struct RegionId(usize);

#[derive(Debug)]
pub struct MlirSafe<'c> {
    ops: Vec<(BlockId, Operation<'c>)>,
    blocks: BTreeMap<BlockId, Block<'c>>,
    regions: BTreeMap<RegionId, Region<'c>>,
    id_counter: usize,
}

impl<'c> MlirSafe<'c> {
    pub fn new() -> Self {
        Self {
            ops: Vec::new(),
            blocks: BTreeMap::new(),
            regions: BTreeMap::new(),
            id_counter: 0,
        }
    }

    pub fn add_op(&mut self, block_id: BlockId, op: Operation<'c>) {
        self.ops.push((block_id, op));
    }

    fn new_id(&mut self) -> usize {
        let id = self.id_counter;
        self.id_counter += 1;
        id
    }

    pub fn new_block(&mut self, arguments: &[(Type<'c>, Location<'c>)]) -> BlockId {
        let id = BlockId(self.new_id());
        let block = Block::new(arguments);
        self.blocks.insert(id, block);
        id
    }

    pub fn new_region(&mut self) -> RegionId {
        let id = RegionId(self.new_id());
        let region = Region::new();
        self.regions.insert(id, region);
        id
    }

    pub fn build_module(self, context: &Context) -> Module<'c> {
        let mut module = Module::new(Location::unknown(context));
        for (block_id, op) in self.ops {
            module.body().append_operation(op);
        }

        module
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use melior::{
        dialect::{arith, func, DialectRegistry},
        ir::{
            attribute::{StringAttribute, TypeAttribute},
            r#type::FunctionType,
        },
        utility::register_all_dialects,
        Context,
    };

    #[test]
    fn simple_test() {
        let context = Context::new();
        let index_type = Type::index(&context);
        let location = Location::unknown(&context);

        let registry = DialectRegistry::new();
        register_all_dialects(&registry);

        context.append_dialect_registry(&registry);
        context.load_all_available_dialects();

        let mut ms = MlirSafe::new();
        let func = func::func(
            &context,
            StringAttribute::new(&context, "add"),
            TypeAttribute::new(
                FunctionType::new(&context, &[index_type, index_type], &[index_type]).into(),
            ),
            {
                let block = Block::new(&[(index_type, location), (index_type, location)]);

                let sum = block.append_operation(arith::addi(
                    block.argument(0).unwrap().into(),
                    block.argument(1).unwrap().into(),
                    location,
                ));

                block.append_operation(func::r#return(&[sum.result(0).unwrap().into()], location));

                let region = Region::new();
                region.append_block(block);
                region
            },
            &[],
            location,
        );

        let current_block = ms.new_block(&[]);
        ms.add_op(current_block, func);

        let module = ms.build_module();
        assert!(module.as_operation().verify());
    }
}
