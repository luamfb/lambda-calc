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
        let filename = match args.next() {
            None => {
                eprintln!("option '{}' requires a file name", arg1);
                return false;
            },
            Some(s) => s,
        };
        parser.set_non_interactive_mode();
        load_file(&filename, parser);
        return false; // never start interactive prompt when -n is used
    } else {
        if !load_file(&arg1, parser) {
            return false;
        }
    }

    // everything else is a file to be loaded.
    for name in args {
        if !load_file(&name, parser) {
            return false;
        }
    }
    true
}

fn load_file(filename: &str, parser: &mut Parser) -> bool {
    if let Err(e) = parser.parse_file(&filename) {
        println!("failed to load file '{}': {}", filename, e);
        return false;
    }
    true
}
