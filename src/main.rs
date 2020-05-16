use clap::{crate_authors, crate_description, crate_version, App, Arg};
use std::io;
use std::path::Path;
use tiger::{
    frame::X86_64,
    parse, print_compiler_errors,
    terminal::{Color, Style},
    tokenize, translate, SourceFile,
};

fn main() {
    let required_file_arg = Arg::with_name("INPUT")
        .value_name("file")
        .help("File to be parsed")
        .takes_value(false)
        .index(1)
        .required(true);

    let matches = App::new("Tiger compiler")
        .author(crate_authors!())
        .version(crate_version!())
        .about(crate_description!())
        .arg(required_file_arg.clone())
        .get_matches();

    let file_name;
    file_name = matches
        .value_of("INPUT")
        .expect("Argument configured wrongly");

    if let Err(e) = run_main(file_name) {
        eprintln!("{}: {}", file_name, e);
        std::process::exit(1);
    }
}

fn run_main(path: impl AsRef<Path>) -> io::Result<()> {
    let source_file = SourceFile::from_path(path.as_ref())?;

    let (tokens, errors) = tokenize(source_file.input());
    print_compiler_errors(&errors, &source_file);
    let mut errors_found = !errors.is_empty();

    let (item, errors) = parse(tokens);
    errors_found |= !errors.is_empty();

    print_compiler_errors(&errors, &source_file);

    if errors_found {
        eprintln!(
            "\n{}{}error:{} Could not compile due to the previous error(s).",
            Color::Red,
            Style::Bold,
            Style::Clear,
        );
    }

    if let Some(item) = item {
        match translate::<X86_64>(item) {
            Ok(e) => println!("{}", e),
            Err(e) => print_compiler_errors(&[e], &source_file),
        }
    }

    Ok(())
}
