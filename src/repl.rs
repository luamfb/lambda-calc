use std::{
    env,
    borrow::Cow,
};
use rustyline::{
    At,
    Cmd,
    CompletionType,
    Context,
    Editor,
    KeyPress,
    Movement,
    Word,
    completion::{Completer, FilenameCompleter, Pair},
    error::ReadlineError,
    highlight::{Highlighter, MatchingBracketHighlighter},
    hint::Hinter,
    line_buffer::LineBuffer,
};
use rustyline_derive::Helper;

use crate::parser::Parser;

#[derive(Helper)]
struct RustylineHelper {
    completer: FilenameCompleter, // for :load
    highlighter: MatchingBracketHighlighter,
}

impl Hinter for RustylineHelper {
    fn hint(&self, _line: &str, _pos:usize, _context: &Context) -> Option<String> {
        None
    }
}

impl Completer for RustylineHelper {
    type Candidate = Pair;

    fn complete(&self, line: &str, pos: usize, context: &Context)
        -> Result<(usize, Vec<Self::Candidate>), ReadlineError>
    {
        self.completer.complete(line, pos, context)
    }
    fn update(&self, line: &mut LineBuffer, start: usize, elected: &str) {
        self.completer.update(line, start, elected)
    }
}

impl Highlighter for RustylineHelper {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool
    ) -> Cow<'b, str> {
        self.highlighter.highlight_prompt(prompt, default)
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        self.highlighter.highlight_hint(hint)
    }

    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str,
        completion: CompletionType
    ) -> Cow<'c, str> {
        self.highlighter.highlight_candidate(candidate, completion)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

fn make_rustyline_editor(histfile: &str) -> Editor<RustylineHelper> {
    let mut rl = Editor::<RustylineHelper>::new();

    let rustyline_helper = RustylineHelper {
        completer: FilenameCompleter::new(),
        highlighter: MatchingBracketHighlighter::new(),
    };
    rl.set_helper(Some(rustyline_helper));

    match rl.load_history(histfile) {
        _ => {}, // ignore errors and keep the compiler happy
    }

    // the cursor doesn't stand still history is being searched...
    // Also, doesn't work when the line is empty for some reason.
    //rl.bind_sequence(KeyPress::Up, Cmd::HistorySearchBackward);
    //rl.bind_sequence(KeyPress::Down, Cmd::HistorySearchForward);

    rl.bind_sequence(KeyPress::ControlRight,
                     Cmd::Move(Movement::ForwardWord(1, At::Start, Word::Vi)));
    rl.bind_sequence(KeyPress::ControlLeft,
                     Cmd::Move(Movement::BackwardWord(1, Word::Vi)));
    rl
}

fn get_histfile_path() -> String {
    let home_key = "HOME";
    let fallback = "/tmp";
    let filename = "lambda_hist";
    match env::var(home_key) {
        Ok(home) => format!("{}/.cache/{}", home, filename),
        Err(e) => {
            eprintln!("warning: failed to read env variable {} ({}), using fallback {}.",
                      home_key, e, fallback);
            format!("{}/{}", fallback, filename)
        },
    }
}

pub fn read_eval_print_loop(mut parser: Parser) {
    let histfile = get_histfile_path();
    let mut rl = make_rustyline_editor(&histfile);

    loop {
        match rl.readline("> ") {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                if let Some(expr) = parser.parse(&line) {
                    println!("= {}", expr);
                    expr.beta_reduce_print(&mut parser);
                }
            },
            Err(ReadlineError::Interrupted) => {
                break;
            },
            Err(ReadlineError::Eof) => {
                break;
            }
            Err(err) => {
                println!("error: {:?}", err);
                break;
            },
        };
    }
    if let Err(_) = rl.save_history(&histfile) {
        eprintln!("failed to save history file");
    };
}
