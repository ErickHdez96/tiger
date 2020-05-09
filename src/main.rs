use std::io;
use std::path::Path;
use tiger::{tokenize, SourceFile, print_compiler_errors};
use clap::{
    App,
    Arg,
    SubCommand,
    crate_authors,
    crate_version,
    crate_description,
    AppSettings,
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
        .subcommand(SubCommand::with_name("lex")
                    .about("runs the lexer and prints the lexemes and errors found")
                    .version("0.1")
                    .author(crate_authors!())
                    .arg(required_file_arg))
        .setting(AppSettings::ArgsNegateSubcommands)
        .setting(AppSettings::SubcommandsNegateReqs)
        .get_matches();

    let file_name;
    let mode;
    if let Some(matches) = matches.subcommand_matches("lex") {
        file_name = matches.value_of("INPUT").expect("Argument configured wrongly");
        mode = Mode::Lex;
    } else {
        file_name = matches.value_of("INPUT").expect("Argument configured wrongly");
        mode = Mode::All;
    }

    if let Err(e) = run_main(file_name, mode) {
        eprintln!("{}: {}", file_name, e);
        std::process::exit(1);
    }
}

fn run_main(path: impl AsRef<Path>, mode: Mode) -> io::Result<()> {
    let source_file = SourceFile::from_path(path.as_ref())?;

    let (_tokens, errors) = tokenize(source_file.input());
    print_compiler_errors(&errors, &source_file);

    if mode == Mode::Lex {
        return Ok(())
    }

    Ok(())
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(u8)]
enum Mode {
    Lex = 0,
    All,
}
