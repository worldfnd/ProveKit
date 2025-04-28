use crate::whir_r1cs::IOPattern;

pub struct GrandProductArgument {}

impl GrandProductArgument {
    pub fn new() -> Self {
        GrandProductArgument {}
    }

    pub fn prove(&self) {
        let io: IOPattern = IOPattern::new("🌪️");
    }
}
