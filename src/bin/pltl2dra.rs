use clap::{ArgGroup, Parser};
use pltl::{
    automata::{AllSubAutomatas, Context},
    pltl::PLTL,
};
// use pltl::automata::{AllSubAutomatas, Context};
// use pltl::pltl::PLTL;
use std::{
    fs::File,
    io::{self, Read, Write},
    path::Path,
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
#[clap(group(
    ArgGroup::new("input_source")
        .required(false)
        .args(&["filein", "input"]),
))]
struct Args {
    #[arg(short = 'I', long)]
    filein: Option<String>,

    #[arg(short = 'i', long)]
    input: Option<String>,

    #[arg(short = 'O', long)]
    fileout: Option<String>,

    #[arg(long)]
    dump_sub: bool,

    #[arg(trailing_var_arg = true)]
    direct_input: Vec<String>,
}

fn main() -> io::Result<()> {
    let args = Args::parse();

    let input = if let Some(file_path) = args.filein {
        if file_path == "-" {
            let mut buffer = String::new();
            io::stdin().read_to_string(&mut buffer)?;
            buffer
        } else {
            let mut file = File::open(file_path)?;
            let mut buffer = String::new();
            file.read_to_string(&mut buffer)?;
            buffer
        }
    } else if let Some(input_str) = args.input {
        input_str
    } else if let Some(direct_input) = args.direct_input.first() {
        direct_input.clone()
    } else {
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer)?;
        buffer
    };

    let (pltl_formula, atom_map) = PLTL::from_string(&input).unwrap();
    let pltl_formula = pltl_formula
        .to_no_fgoh()
        .to_negation_normal_form()
        .simplify();
    let ctx = Context::new(&pltl_formula, &atom_map);

    let automatas = AllSubAutomatas::new(&ctx, &atom_map);
    let files = automatas.to_files();

    for (name, content) in files {
        let path = Path::new(&args.fileout.clone().unwrap_or_default()).join(name);
        let mut file = File::create(path)?;
        file.write_all(content.as_bytes())?;
    }
    Ok(())
}
