/// Commands understood by the parser.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Command {
    Help,
    Load,
    Define, // :=, pseudo-command
}

pub struct CommandClassifier<'a> {
    pub short_name: &'a str,
    pub long_name: &'a str,
    pub cmd: Command,
    pub arg_expected: bool,
    description: &'a str,
}

pub const COMMAND_CLASSIFIER : &[CommandClassifier] = &[
    CommandClassifier {
        short_name: "h",
        long_name: "help",
        cmd: Command::Help,
        arg_expected: false,
        description: "print this message.",
    },
    CommandClassifier {
        short_name: "l",
        long_name: "load",
        cmd: Command::Load,
        arg_expected: true,
        description: "parse all lines from a file.",
    },
];

pub fn print_usage() {
    println!(
    "A lambda calculus interpreter.
    See <TODO link to documentation> for details.

    Available commands:"
    );
    for command in COMMAND_CLASSIFIER {
        println!(":{}, :{}\t{}",
                 command.short_name,
                 command.long_name,
                 command.description);
    }
}
