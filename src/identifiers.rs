pub type ID = usize;

#[derive(Default, Clone, Debug)]
pub struct IDGenerator {
    counter: usize,
}

impl IDGenerator {
    pub fn new_id<T: From<usize> + Copy>(&mut self) -> T {
        let new_id = self.counter;
        self.counter += 1;
        T::from(new_id)
    }
}
