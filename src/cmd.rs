/// Commands understood by the parser.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Command {
    Help,
    Load,
    Define, // :=, pseudo-command
    Pause,
    Step,
    CountSteps,
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
        arg_expected: true,
        description: "Whether to wait, before each reduction step, until the user presses Enter."
    },
    CommandClassifier {
        short_name: "s",
        long_name: "step",
        cmd: Command::Step,
        arg_expected: true,
        description: "Whether to print each step of beta reduction or only the final result."
    },
    CommandClassifier {
        short_name: "c",
        long_name: "count",
        cmd: Command::CountSteps,
        arg_expected: true,
        description: "Whether to print the number of steps taken, which includes beta reductions and symbol substitutions."
    },
];

pub fn print_usage() {
    println!(
"An untyped lambda calculus interpreter.
See <https://docs.rs/lambda_calc> for the syntax understood by the parser.

Usage:
<program_name> -h | --help
\tPrint this message.
<program_name> [file1] [file2] ...
\tStart the interactive interpreter, optionally loading the files named
\tfile1, file2, ... as if by using the :load command.
<program_name> -n filename
\tNon-interactive mode: load a single file named filename and print output in
\ta program-friendly way, which means only ASCII characters and no color.

Interactive commands:"
    );
    for command in COMMAND_CLASSIFIER {
        println!(":{}, :{}\n\t{}",
                 command.short_name,
                 command.long_name,
                 command.description);
    }
}
