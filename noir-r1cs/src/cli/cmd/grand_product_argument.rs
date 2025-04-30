use {super::Command, anyhow::Result, argh::FromArgs, noir_r1cs::FieldElement, tracing::instrument};
use noir_r1cs::GrandProductArgument;

/// Prove a prepared Noir program
#[derive(FromArgs, PartialEq, Debug)]
#[argh(subcommand, name = "grand-product-argument")]
pub struct Args {
    // /// path to the compiled Noir program
    // #[argh(positional)]
    // scheme_path: PathBuf,

    // /// path to the proof file
    // #[argh(positional)]
    // proof_path: PathBuf,
}



impl Command for Args {
    #[instrument(skip_all)]
    fn run(&self) -> Result<()> {
        let array_to_prove = (2..=129).map(|x| FieldElement::from(x as u64)).collect::<Vec<_>>();
        let gpa = GrandProductArgument::new(array_to_prove);
        gpa.prove();
        Ok(()) // Ensure compatibility with EarlyExit
    }
}
