use std::{env, fs, io::Write as _, path::{self, PathBuf}, process::ExitCode};

use clap::Parser;
use struktur::{ast::{self, Ast}, /* codegen::emit, cps::transform_cps ,*/ error::CompileError, parse::parse, stage::Typed, symbols::{self, resolve_symbols}, types::{pretty_print::pretty_print, type_check}};
use miette::{NamedSource, Report};

#[derive(Debug, Parser)]
#[command(version = "1", about = "Compiles a Struktur source file.")]
struct Args {
    /// Path to the input file.
    #[arg(value_parser = file_exists)]
    input: PathBuf,

    /// Path to output the resulting Javascript file to.
    /// If omitted, the output file will be a sibling of the input file
    /// with the same name and a `.js` extension.
    #[arg()]
    output: Option<PathBuf>,

    /// Only compile the input file and do not perform codegen.
    #[arg(short = 'b', long = "build")]
    no_run: bool,

    /// Print the types of all top-level bindings in the compiled program.
    #[arg(long = "types")]
    types: bool,

    /// Print CPS structure of compiled program.
    /// Only relevant if `--no-run` is not specified.
    #[arg(long = "cps")]
    cps: bool,
}

fn file_exists(s: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(s);

    if !path.exists() {
        return Err("path does not exist".to_owned());
    }

    if !path.is_file() {
        return Err("path is not a file".to_owned())
    }

    Ok(path)
}

fn main() -> Result<ExitCode, anyhow::Error> {
    let args = Args::parse();

    let cwd = env::current_dir()?;

    let input_path = path::absolute(&args.input)?;
    let input_display = pathdiff::diff_paths(&input_path, &cwd).unwrap()
        .to_string_lossy().into_owned();

    let output_path = match &args.output {
        Some(path) => path::absolute(path)?,
        None => {
            let mut path = input_path.clone();
            path.set_extension("js");
            path
        }
    };
    let output_display = pathdiff::diff_paths(&output_path, &cwd).unwrap()
        .to_string_lossy().into_owned();

    let text = fs::read_to_string(&args.input)?;
    let source = NamedSource::new(
        args.input.to_string_lossy().into_owned(),
        text
    );

    let ast = match compile(&source) {
        Ok(ast) => ast,
        Err(e) => {
            println!("{:?}", Report::from(e).with_source_code(source));
            return Ok(ExitCode::FAILURE);
        }
    };

    if args.types {
        for item in &ast.root().0 {
            match &item.0 {
                ast::ItemVal::Binding(binding) => {
                    let symbol = match ast.symbols().get(binding.symbol) {
                        symbols::SymbolKind::Binding(symbol) => symbol,
                        _ => unreachable!()
                    };

                    let name = &symbol.name;
                    let ty = pretty_print(&symbol.data.ty);
                    println!("{} : {}", name, ty);
                }
            }
        }

        println!();
    }

    if args.no_run {
        return Ok(ExitCode::SUCCESS);
    }

    /*
    let cps = transform_cps(&ast);

    if args.cps {
        println!("{cps:#?}");
    }

    let out = emit(&cps);

    println!("{} -> {}", input_display, output_display);

    if let Some(dir) = output_path.parent() {
        fs::create_dir_all(dir)?;
    }
    let mut out_file = fs::File::create(&output_path)?;
    out_file.write_all(out.as_bytes())?;
    */

    Ok(ExitCode::SUCCESS)
}

fn compile(source: &NamedSource<String>) -> Result<Ast<Typed>, CompileError> {
    let parsed = parse(source.inner())?;
    let sem = resolve_symbols(&parsed)?;
    let typed = type_check(&sem)?;

    Ok(typed)
}
