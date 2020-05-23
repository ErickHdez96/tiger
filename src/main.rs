use clap::{crate_authors, crate_description, crate_version, App, Arg};
use std::io;
use std::path::Path;
use tiger::{
    canon::{basic_blocks, linearize, trace_schedule},
    codegen::CodeGen,
    frame::{Fragment, Frame, X86_64},
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

    let fragments = match item.map(translate::<X86_64>) {
        Some(Ok(f)) => f,
        Some(Err(e)) => {
            print_compiler_errors(&[e], &source_file);
            errors_found = true;
            vec![]
        }
        None => vec![],
    };

    if errors_found {
        eprintln!(
            "\n{}{}error:{} Could not compile due to the previous error(s).",
            Color::Red,
            Style::Bold,
            Style::Clear,
        );
        std::process::exit(1);
    }

    for fragment in fragments {
        match fragment {
            Fragment::Procedure { body, frame } => {
                let body = frame.borrow().proc_entry_exit_1(body);
                let statements = linearize(*body);
                let (blocks, done_label) = basic_blocks(statements);
                let statements = trace_schedule(blocks, done_label);

                let mut gen = CodeGen::new();
                for statement in statements {
                    gen.munch_stmt(*statement);
                }

                let instructions = gen.into_instructions();
                let instructions = frame.borrow().proc_entry_exit_2(instructions);
                let procedure = frame.borrow().proc_entry_exit_3(instructions);

                println!("{}", procedure);
            }
            Fragment::String(label, s) => println!("{}: {}", label, s.as_str()),
        }
    }

    Ok(())
}
