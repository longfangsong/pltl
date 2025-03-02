use clap::{ArgGroup, Parser};
use hoars::output::to_hoa;
use pltl::automata::{Context, State};
use pltl::pltl::PLTL;
use std::fs::File;
use std::io::{self, Read, Write};

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

    let (pltl_formula, atom_map) = PLTL::from_string(&input);

    let context = Context::new(&pltl_formula, atom_map);
    let initial_state = State::new(&context);

    let all_letters = context.atom_map.right_values().cloned().collect();
    let automaton =
        initial_state.dump_automata(&context, &all_letters);

    let hoa_automaton = automaton.dump_hoa(&format!("\"{pltl_formula}\""));
    let output = to_hoa(&hoa_automaton);

    if let Some(file_path) = args.fileout {
        if file_path == "-" {
            io::stdout().write_all(output.as_bytes())?;
        } else {
            let mut file = File::create(file_path)?;
            file.write_all(output.as_bytes())?;
        }
    } else {
        io::stdout().write_all(output.as_bytes())?;
    }

    Ok(())
}
