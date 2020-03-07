use std::env;
use crate::{
    cmd,
    parser::Parser,
};

// returns true if the REPL should be run afterwards, false otherwise.
pub fn parse_cmdline_options(parser: &mut Parser) -> bool {
    let mut args = env::args();

    // skip program name
    if let None = args.next() {
        return true;
    }

    let arg1 = match args.next() {
        None => return true,
        Some(s) => s,
    };
    if arg1 == "-h" || arg1 == "--help" {
        cmd::print_usage();
        return false;
    } else if arg1 == "-n" || arg1 == "--no-interactive" {
        parser.set_non_interactive_mode();
        load_file(args.next(), parser);
        return false; // never start interactive prompt when -n is used
    } else {
        if !load_file(Some(arg1), parser) {
            return false;
        }
    }

    // everything else is a file to be loaded.
    for name in args {
        if !load_file(Some(name), parser) {
            return false;
        }
    }
    true
}

fn load_file(filename: Option<String>, parser: &mut Parser) -> bool {
    let name = match filename {
        None => "stdin".to_string(),
        Some(ref s) => s.clone(),
    };
    if let Err(e) = parser.parse_file(filename) {
        eprintln!("failed to load file '{}': {}", &name, e);
        return false;
    }
    true
}
