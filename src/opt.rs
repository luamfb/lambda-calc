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
    } else if arg1 == "-l" || arg1 == "--load" {
        return load_opt(args, parser);
    }
    println!("unknown command-line argument '{}'", arg1);
    false
}

fn load_opt(mut args: env::Args, parser: &mut Parser) -> bool {
    match args.next() {
        None => {
            eprintln!("load command requires an argument.");
            false
        },
        Some(s) => {
            if let Err(e) = parser.parse_file(&s) {
                println!("failed to load file '{}': {}", s, e);
                return false;
            }
            true
        }
    }
}
