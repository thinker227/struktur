use std::path::PathBuf;

use clap::{Arg, ArgAction, ArgMatches, Command, crate_version};

#[derive(Debug)]
pub struct Args {
    pub input: PathBuf,
    pub output: Option<PathBuf>,
    pub build: bool,
    pub ast: bool,
    pub types: bool,
    pub cps: bool,
    pub quiet: bool,
}

impl From<ArgMatches> for Args {
    fn from(matches: ArgMatches) -> Self {
        Self {
            input: matches.get_one::<PathBuf>("input").unwrap().clone(),
            output: matches.get_one::<PathBuf>("output").cloned(),
            build: matches.get_flag("build"),
            ast: matches.get_flag("ast"),
            types: matches.get_flag("types"),
            cps: matches.get_flag("cps"),
            quiet: matches.get_flag("quiet"),
        }
    }
}

pub fn root_command() -> Command {
    Command::new("struktur")
        .about("Struktur compiler")
        .version(crate_version!())
        .arg_required_else_help(true)
        .disable_help_subcommand(true)
        .args_conflicts_with_subcommands(true)
        .arg(
            Arg::new("input")
                .help("Path to the input file to compile")
                .required(true)
                .value_parser(file_exists),
        )
        .arg(
            Arg::new("output")
                .help("Path to output the resulting Javascript file to")
                .long_help("Path to output the resulting Javascript file to. If omitted, the output file will be a sibling of the input file with the same name and a `.js` extension")
                .required(false)
                .value_parser(file),
        )
        .arg(
            Arg::new("build")
                .help("Only compile the input file and do not perform codegen")
                .short('b')
                .long("build")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("ast")
                .help("Output the abstract syntax tree of the compiled program to a `.ast.yml` file")
                .long("ast")
                .action(ArgAction::SetTrue)
        )
        .arg(
            Arg::new("types")
                .help("Print the types of all top-level bindings in the compiled program")
                .long("types")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("cps")
                .help("Output the CPS structure of the compiled program to a `.cps.yml` file")
                .long("cps")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("quiet")
                .help("Do not print any extraneous information")
                .long_help("Do not print any extraneous information\nWill still print compilation errors, internal compiler crashes, and requested intermediate compilation output (such as `--types`)")
                .short('q')
                .long("quiet")
                .action(ArgAction::SetTrue)
        )
}

fn file(s: &str) -> Result<PathBuf, String> {
    if s.is_empty() {
        Err("path is empty".to_owned())
    } else {
        Ok(PathBuf::from(s))
    }
}

fn file_exists(s: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(s);

    if !path.exists() {
        return Err("path does not exist".to_owned());
    }

    if !path.is_file() {
        return Err("path is not a file".to_owned());
    }

    Ok(path)
}
