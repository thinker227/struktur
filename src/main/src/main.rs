use std::{env, fs, io::Write as _};

use struktur::{codegen::emit, cps::transform_cps, parse::parse, symbols::resolve_symbols, types::type_check};
use miette::{NamedSource, Report};

fn main() {
    let args = env::args().skip(1).collect::<Vec<_>>();
    let path = &args[0];
    let out_path = &args[1];
    let text = fs::read_to_string(path).unwrap();
    let source = NamedSource::new(path, text);

    let parsed = match parse(source.inner()) {
        Ok(x) => x,
        Err(e) => {
            let report = Report::from(e)
                .with_source_code(NamedSource::new(path, source));
            println!("{:?}", report);
            return;
        }
    };

    let sem = resolve_symbols(&parsed);

    let typed = type_check(&sem);

    let cps = transform_cps(&typed);

    let out = emit(&cps);

    let mut out_file = fs::File::create(&out_path).unwrap();
    out_file.write_all(out.as_bytes()).unwrap();
}
