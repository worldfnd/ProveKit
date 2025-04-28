use {super::Command, anyhow::Result, argh::FromArgs, tracing::instrument};
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
        let gpa = GrandProductArgument::new();
        gpa.prove();
        Ok(()) // Ensure compatibility with EarlyExit
    }
}
