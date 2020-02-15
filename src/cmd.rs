/// Commands understood by the parser.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Command {
    Help,
    Load,
    Define, // :=, pseudo-command
    Pause,
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
    CommandClassifier {
        short_name: "p",
        long_name: "pause",
        cmd: Command::Pause,
        arg_expected: false,
        description: "toggle pause mode, in which the user must press Enter before each reduction step"
    },
];

pub fn print_usage() {
    println!(
"A lambda calculus interpreter.
See <https://docs.rs/lambda_calc> for details.

Available commands:"
    );
    for command in COMMAND_CLASSIFIER {
        println!(":{}, :{}\t{}",
                 command.short_name,
                 command.long_name,
                 command.description);
    }
}
