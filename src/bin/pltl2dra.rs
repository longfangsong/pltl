use clap::{ArgGroup, Parser};
use pltl::automata::hoa::output::to_hoa;
use pltl::automata::{AllSubAutomatas, Context, State};
use pltl::pltl::PLTL;
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::path::Path;

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

    let (pltl_formula, atom_map) = PLTL::from_string(&input);
    let pltl_formula = pltl_formula.normal_form();
    let context = Context::new(&pltl_formula, atom_map);

    if args.dump_sub {
        if let Some(output_dir) = &args.fileout {
            if !Path::new(output_dir).exists() {
                fs::create_dir_all(output_dir)?;
            }

            let all_sub_automatas = AllSubAutomatas::new(&context);
            all_sub_automatas.to_files(&context, output_dir);

            return Ok(());
        } else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Must specify output directory with -O",
            ));
        }
    } else {
        let initial_state = State::new(&context);

        let automaton = initial_state.dump_automata(&context, context.atom_map.len());

        let hoa_automaton = automaton.dump_hoa(&format!(
            "\"{}\"",
            pltl_formula.format_with_atom_names(&context.atom_map)
        ));
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
    }

    Ok(())
}
