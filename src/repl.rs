use std::{
    env,
    borrow::Cow,
    cell::RefCell,
    rc::Rc,
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

use crate::{
    parser::Parser,
    lexer,
    cmd::{Command, CommandClassifier, COMMAND_CLASSIFIER},
};

#[derive(Helper)]
struct RustylineHelper {
    filename_completer: FilenameCompleter, // for :load
    highlighter: MatchingBracketHighlighter,
    parser: Rc<RefCell<Parser>>,
}

impl Hinter for RustylineHelper {
    fn hint(&self, _line: &str, _pos:usize, _context: &Context) -> Option<String> {
        None
    }
}

impl Completer for RustylineHelper {
    type Candidate = Pair;

    fn complete(&self, line: &str, cursor_pos: usize, context: &Context)
        -> Result<(usize, Vec<Self::Candidate>), ReadlineError>
    {
        let null_completion = (0, Vec::with_capacity(0));
        if cursor_pos == 0 {
            return Ok(null_completion);
        }
        let completion = match line.chars().next() {
            None => Ok(null_completion),
            Some(':') => {
                let compl_str = &line[1..cursor_pos];
                let completion = match compl_str.chars().position(|c| c == ' ') {
                    None => {
                        // no space: complete the command's name.
                        match get_command_starts_with(compl_str) {
                            None => Ok(null_completion),
                            Some(cmd) => {
                                let compl_pair = Pair {
                                    display: cmd.long_name.to_string(),
                                    replacement: cmd.long_name.to_string(),
                                };
                                Ok((1, vec![compl_pair]))
                            },
                        }
                    },
                    Some(pos) => {
                        // with space: complete the argument's name.
                        match get_command(&compl_str[..pos]) {
                            None => Ok(null_completion),
                            Some(class) => {
                                if let Command::Load = class.cmd {
                                  self.filename_completer.complete(line, cursor_pos, context)
                                } else {
                                    // we only handle the load command's completion for now.
                                    Ok(null_completion)
                                }
                            },
                        }
                    },
                };
                completion
            },
            Some(_) => {
                let word_begin = get_start_word_under_cursor(&line, cursor_pos);
                let completion: Vec<Pair> = self.parser
                    .borrow()
                    .get_symbol_names_with_prefix(&line[word_begin..cursor_pos])
                    .iter()
                    .map(|s| Pair { display: s.to_string(), replacement: s.to_string(), })
                    .collect();
                Ok((word_begin, completion))
            },
        };
        completion
    }
    fn update(&self, line: &mut LineBuffer, start: usize, elected: &str) {
        self.filename_completer.update(line, start, elected)
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

fn make_rustyline_editor(histfile: &str, parser: Rc<RefCell<Parser>>) -> Editor<RustylineHelper> {
    let mut rl = Editor::<RustylineHelper>::new();

    let rustyline_helper = RustylineHelper {
        filename_completer: FilenameCompleter::new(),
        highlighter: MatchingBracketHighlighter::new(),
        parser,
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

pub fn read_eval_print_loop(parser: Parser) {

    let parser = Rc::new(RefCell::new(parser));

    let histfile = get_histfile_path();
    let mut rl = make_rustyline_editor(&histfile, Rc::clone(&parser));

    loop {
        match rl.readline("> ") {
            Ok(mut line) => {
                while lexer::strip_whitespace_and_line_cont(&mut line) {
                    match rl.readline("& ") {
                        Ok(new_line) => line.push_str(&new_line),
                        Err(ReadlineError::Interrupted) | Err(ReadlineError::Eof) => break,
                        Err(err) => {
                            eprintln!("error: {:?}", err);
                            break;
                        },
                    };
                }
                rl.add_history_entry(line.as_str());
                let mut parser_mut_ref = parser.borrow_mut();
                match parser_mut_ref.parse(&line, None) {
                    Ok(ast) => if let Some(expr) = ast {
                        expr.beta_reduce_print(&parser_mut_ref);
                    },
                    Err(e) => eprintln!("syntax error: {}", e),
                };
            },
            Err(ReadlineError::Interrupted) => {
                break;
            },
            Err(ReadlineError::Eof) => {
                break;
            }
            Err(err) => {
                eprintln!("error: {:?}", err);
                break;
            },
        };
    }
    if let Err(_) = rl.save_history(&histfile) {
        eprintln!("failed to save history file");
    };
}

// find the beginning of the word in line which is currently under the cursor,
// whose position is cursor_pos.
//
fn get_start_word_under_cursor(line: &str, cursor_pos: usize) -> usize {
    let mut chars = line[..cursor_pos].chars();
    let mut res = cursor_pos;
    while let Some(c) = chars.next_back() {
        if c == ' ' || c == '(' || c == ')' {
            break
        }
        res -= c.len_utf8();
    };
    // if iter == None, res == 0.
    res
}

// get the command entry in COMMAND_CLASSIFIER whose long name starts with prefix.
fn get_command_starts_with(prefix: &str) -> Option<&CommandClassifier> {
    for class in COMMAND_CLASSIFIER {
        if class.long_name.starts_with(prefix) {
            return Some(&class);
        }
    }
    None
}

fn get_command(name: &str) -> Option<&CommandClassifier> {
    for class in COMMAND_CLASSIFIER {
        if name == class.short_name || name == class.long_name {
            return Some(&class);
        }
    }
    None
}
