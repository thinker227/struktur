use std::{
    env,
    fs::{self, File},
    panic,
    path::{self, Path, PathBuf},
    process::ExitCode,
    sync::Arc,
};

use anyhow::Context;
use struktur::{
    sources::{Source, SourceName, SourceProject},
    syntax::{NodeMap, SyntaxNode, lex::lex, parse::parse},
};

use crate::{
    cli::{Args, root_command},
    logger::Logger,
};

use error::Error;

mod cli;
mod error;
mod logger;

fn main() -> ExitCode {
    let args: Args = root_command().get_matches().into();

    let logger = Arc::new(Logger::new(args.quiet));

    {
        let logger = logger.clone();
        panic::set_hook(Box::new(move |panic| {
            let payload = panic
                .payload_as_str()
                .unwrap_or("(no panic payload)")
                .to_owned();

            // We don't *really* care about panicing here? We're already panicing lol
            elog!(logger, "Panic", "{payload}").unwrap();
        }));
    }

    let result = execute(&args, &logger);

    match result {
        Ok(code) => code,
        Err(error) => {
            elog!(&logger, "Crash", "{error:?}").unwrap();
            ExitCode::FAILURE
        }
    }
}

fn execute(args: &Args, logger: &Logger) -> anyhow::Result<ExitCode> {
    let pwd = env::current_dir().with_context(|| "Failed to get current working directory")?;

    // The input path from the CLI has been verified to not been empty,
    // and the only other documented way that `path::absolute` can fail is if failing to get the current working directory,
    // but we already have the current working directory, so this should never fail.
    let input_path = path::absolute(&args.input).unwrap();
    let input_display = pathdiff::diff_paths(&input_path, &pwd).unwrap();

    let output_path = match &args.output {
        // Much same reasoning as with `path::absolute` above.
        Some(path) => path::absolute(path).unwrap(),
        None => sibling_file_path(&input_path, "js"),
    };
    let _output_display = pathdiff::diff_paths(&output_path, &pwd).unwrap();

    let text = fs::read_to_string(&input_path).with_context(|| {
        format!(
            "Failed to read source file {}",
            input_path.to_string_lossy()
        )
    })?;

    let mut sources = SourceProject::new();
    let source = sources.add(SourceName::File(input_display.clone()), text);

    let result = compile(
        &pwd,
        &input_path,
        source,
        args.build,
        args.ast,
        args.types,
        args.cps,
        logger,
    );

    match result {
        Ok(_) => Ok(ExitCode::SUCCESS),
        Err(Error::Diagnostic(diagnostic)) => {
            diagnostic.report().eprint(&sources)?;
            Ok(ExitCode::FAILURE)
        }
        Err(Error::Other(other)) => Err(other),
    }
}

fn sibling_file_path(path: &Path, extension: &str) -> PathBuf {
    let mut path = PathBuf::from(path);
    path.set_extension(extension);
    path
}

#[allow(clippy::too_many_arguments)]
fn compile(
    pwd: &Path,
    input_path: &Path,
    source: &Source,
    _no_run: bool,
    print_ast: bool,
    _print_types: bool,
    _print_cps: bool,
    logger: &Logger,
) -> Result<(), Error> {
    log!(logger, "Compiling", "{}", source.name())?;

    let mut nodes = NodeMap::with_key();

    let tokens = lex(source)?;
    let root_id = parse(&mut nodes, tokens)?;

    let root = SyntaxNode::new(&nodes, root_id);

    if print_ast {
        let ast_path = sibling_file_path(input_path, "ast.yml");
        let ast_display = pathdiff::diff_paths(&ast_path, pwd).unwrap();

        let ast_file = File::create(&ast_path).with_context(|| {
            format!(
                "Failed to create AST output file {}",
                ast_path.to_string_lossy()
            )
        })?;
        serde_yml::to_writer(&ast_file, &root).with_context(|| {
            format!(
                "Failed to write to AST output file {}",
                ast_path.to_string_lossy()
            )
        })?;

        log!(
            logger,
            "AST",
            "written to {}",
            ast_display.to_string_lossy()
        )?;
    }

    Ok(())
}
