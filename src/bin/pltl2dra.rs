use clap::{Parser, ArgGroup};
use std::path::PathBuf;
use std::fs::File;
use std::io::{self, Read, Write};
use std::collections::HashSet;
use pltl::pltl::{parse, PLTL};
use pltl::automata::{Context, State};
use hoars::output::to_hoa;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
#[clap(group(
    ArgGroup::new("input_source")
        .required(false)
        .args(&["filein", "input"]),
))]
struct Args {
    // #[arg(short = 'a', long)]
    // annotations: bool,

    #[arg(short = 'I', long)]
    filein: Option<String>,

    #[arg(short = 'i', long)]
    input: Option<String>,

    #[arg(short = 'O', long)]
    fileout: Option<String>,

    // #[arg(short = 'p', long)]
    // parallel: bool,

    // #[arg(short = 'w', long)]
    // worker: Option<usize>,

    // #[arg(short = 'c', long)]
    // complete: bool,

    // #[arg(short = 'na', long = "noacceptance")]
    // no_acceptance: bool,

    // #[arg(short = 'ne', long = "noeager")]
    // no_eager: bool,

    // #[arg(short = 'np', long = "nosuspend")]
    // no_suspend: bool,

    // #[arg(short = 'ns', long = "nosupport")]
    // no_support: bool,

    #[arg(last = true)]
    direct_input: Option<String>,
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
    } else if let Some(direct_input) = args.direct_input {
        direct_input
    } else {
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer)?;
        buffer
    };

    /* 1 */
    // 解析 PLTL 公式
    let pltl_formula = match parse(&input) {
        Ok((rest, formula)) => formula.normal_form(),
        Err(e) => {
            eprintln!("解析 PLTL 公式时出错: {}", e);
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "无效的 PLTL 公式"));
        }
    };
    
    // 提取公式中的原子命题
    let atoms = extract_atoms(&pltl_formula);
    
    // 创建上下文和初始状态
    let context = Context::new(&pltl_formula);
    let initial_state = State::new(&context);
    
    // 生成自动机
    let automaton = initial_state.dump_automata(&context, &atoms);
    
    // 转换为 HOA 格式
    let hoa_automaton = automaton.dump_hoa(&pltl_formula.to_string());
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

fn extract_atoms(formula: &PLTL) -> HashSet<String> {
    let mut atoms = HashSet::new();
    
    match formula {
        PLTL::Atom(name) => {
            atoms.insert(name.clone());
        },
        PLTL::Unary(_, subformula) => {
            atoms.extend(extract_atoms(subformula));
        },
        PLTL::Binary(_, left, right) => {
            atoms.extend(extract_atoms(left));
            atoms.extend(extract_atoms(right));
        },
        _ => {}
    }
    
    atoms
}
