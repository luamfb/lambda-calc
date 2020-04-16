use crate::cmd::{
    Command,
    COMMAND_CLASSIFIER,
};

/// Tokens understood by the parser.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<'a> {
    Invalid(char),
    Id(&'a str),
    Def,
    Gives,
    Lambda,
    OpenParen,
    CloseParen,
    Strict,
    Command(Command),
}

/// Removes whitespace and line continuation token (if any) from the end
/// of a line, returning whether there was a line continuation token.
///
pub fn strip_whitespace_and_line_cont(line: &mut String) -> bool {
    while let Some(c) = line.chars().next_back() {
        if !c.is_whitespace() {
            break;
        }
        line.pop();
    }
    match line.chars().next_back() {
        Some('&') => {
            line.pop();
            true
        },
        _ => false,
    }
}

/// An iterator over the tokens of a string. Used by Parser.
///
/// These tokens are all considered the same:
///
/// ```
/// # use lambda_calc::lexer::TokenIter;
/// let t1 = TokenIter::new("λ");
/// let t2 = TokenIter::new("lambda");
/// let t3 = TokenIter::new("\\"); // backslash, Haskell-like
///
/// assert_eq!(t1.clone().next(), t2.clone().next());
/// assert_eq!(t1.clone().next(), t3.clone().next());
/// ```
///
/// As are these:
///
/// ```
/// # use lambda_calc::lexer::TokenIter;
/// // separate the variables from the body in a lambda term
/// let t1 = TokenIter::new(".");
/// let t2 = TokenIter::new("->");
/// let t3 = TokenIter::new("=>");
///
/// assert_eq!(t1.clone().next(), t2.clone().next());
/// assert_eq!(t1.clone().next(), t3.clone().next());
/// ```
///
/// Comments start with '#' and extend until the end of line:
/// ```
/// # use lambda_calc::lexer::TokenIter;
/// let t1 = TokenIter::new("# This is a comment");
///
/// assert_eq!(t1.clone().next(), None);
/// ```
///
#[derive(Clone)]
pub struct TokenIter<'a> {
    s: &'a str,
    pos: usize,
    cmd_arg_expected: bool,
}

impl<'a> Iterator for TokenIter<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Token<'a>> {
        self.consume_whitespace();

        let rest_of_string = self.rest_of_string();
        if rest_of_string.is_empty() {
            return None;
        }
        if self.cmd_arg_expected {
            self.cmd_arg_expected = false;
            self.pos += rest_of_string.len();
            let cmd_arg = rest_of_string.trim();
            if cmd_arg.is_empty() {
                return None;
            }
            return Some(Token::Id(cmd_arg));
        }

        {
            let first_char = rest_of_string.chars().next()?;
            if first_char == ':' {
                self.pos += 1; // skip ':'
                return match self.get_command() {
                    Some(cmd) => {
                        if let Command::Define = cmd {
                            Some(Token::Def)
                        } else {
                            Some(Token::Command(cmd))
                        }
                    },
                    None => Some(Token::Invalid(first_char)),
                };
            } else if first_char == '#' {
                // comment; skip to the end of line.
                self.pos = self.s.len();
                return None;
            }
        }

        // The order matters in those lists: if one token is prefix of another,
        // the largest one must come first.
        //
        let classifier = &[
            (vec!["=>", "->", "."],     Token::Gives),
            (vec!["="],                 Token::Def),
            (vec!["λ", "\\", "lambda"], Token::Lambda),
            (vec!["("],                 Token::OpenParen),
            (vec![")"],                 Token::CloseParen),
            (vec!["!"],                 Token::Strict),
            // anything else is either a Id or an invalid token.
        ];
        for (names, token_class) in classifier {
            for name in names {
                if rest_of_string.starts_with(name) {
                    self.pos += name.len();
                    return Some(token_class.clone());
                }
            }
        }

        // if we're here, it could be a var or an invalid token.

        let token_class = self.handle_var_or_invalid();
        Some(token_class)
    }
}

impl<'a> TokenIter<'a> {
    pub fn new(s: &'a str) -> TokenIter<'a> {
        TokenIter {
            s,
            pos: 0,
            cmd_arg_expected: false,
        }
    }

    fn rest_of_string(&self) -> &'a str {
        &self.s[self.pos..]
    }

    fn consume_whitespace(&mut self) {
        let rest_of_string = self.rest_of_string();
        for c in rest_of_string.chars() {
            if !c.is_whitespace() {
                break
            }
            self.pos += c.len_utf8();
        }
    }

    fn handle_var_or_invalid(&mut self) -> Token<'a> {
        let rest_of_string = self.rest_of_string();
        if rest_of_string.is_empty() {
            panic!("TokenIter.next(): rest_of_string is empty");
        }

        let (name_len, last_char) = self.get_next_word_and_last_char();

        if name_len == 0 {
            // we must increment position here too, otherwise we'll yield
            // the same invalid token forever.
            // Note that each invalid token we yield has 1 char only.
            //
            self.pos += last_char.len_utf8();
            Token::Invalid(last_char)
        } else {
            self.pos += name_len;
            Token::Id(&rest_of_string[0..name_len])
        }
    }

    fn get_command(&mut self) -> Option<Command> {
        let rest_of_string = self.rest_of_string();
        if let Some('=') = rest_of_string.chars().next() {
            self.pos += 1;
            return Some(Command::Define); // ":="
        }

        let (name_len, _) = self.get_next_word_and_last_char();
        let name = &rest_of_string[0..name_len];
        for class in COMMAND_CLASSIFIER {
            if name == class.short_name || name == class.long_name {
                self.pos += name.len();
                self.cmd_arg_expected = class.arg_expected;
                return Some(class.cmd);
            }
        }
        None
    }

    fn get_next_word_and_last_char(&self) -> (usize, char) {
        let rest_of_string = self.rest_of_string();
        let mut name_len = 0;
        let mut last_char:char = '\0';

        for c in rest_of_string.chars() {
            last_char = c;
            if !c.is_alphabetic() && c != '_' {
                break
            }
            name_len += c.len_utf8();
        }
        (name_len, last_char)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_token_single_char() {
        let s = "=";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Def));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn single_token_utf8() {
        let s = "λ";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Lambda));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn single_token_multi_char() {
        let s = "lambda";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Lambda));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn single_token_command() {
        let s = ":load";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Command(Command::Load)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn single_token_pseudo_command() {
        let s = ":=";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Def));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn command_arg_single_word() {
        let s = ":load foo";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Command(Command::Load)));
        assert_eq!(iter.next(), Some(Token::Id("foo")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn command_arg_multi_word() {
        let s = ":load foo bar baz";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Command(Command::Load)));
        assert_eq!(iter.next(), Some(Token::Id("foo bar baz")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn token_prefix_of_another() {
        let s = "=>:===>";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Gives)); // =>
        assert_eq!(iter.next(), Some(Token::Def)); // :=
        assert_eq!(iter.next(), Some(Token::Def)); // =
        assert_eq!(iter.next(), Some(Token::Gives)); // =>
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn multi_tokens_consecutive() {
        let s = "f=>(x)";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Id("f")));
        assert_eq!(iter.next(), Some(Token::Gives));
        assert_eq!(iter.next(), Some(Token::OpenParen));
        assert_eq!(iter.next(), Some(Token::Id("x")));
        assert_eq!(iter.next(), Some(Token::CloseParen));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn multi_tokens_whitespace() {
        let s = "  f   x=    x";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Id("f")));
        assert_eq!(iter.next(), Some(Token::Id("x")));
        assert_eq!(iter.next(), Some(Token::Def));
        assert_eq!(iter.next(), Some(Token::Id("x")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn comment_beginning_line() {
        let s = "# comment";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn comment_whitespace() {
        let s = "   # comment";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn comment_after_valid_tokens() {
        let s = "lambda x . x # comment";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Lambda));
        assert_eq!(iter.next(), Some(Token::Id("x")));
        assert_eq!(iter.next(), Some(Token::Gives));
        assert_eq!(iter.next(), Some(Token::Id("x")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn strict_var() {
        let s = "\\!x -> x";
        let mut iter = TokenIter::new(s);
        assert_eq!(iter.next(), Some(Token::Lambda));
        assert_eq!(iter.next(), Some(Token::Strict));
        assert_eq!(iter.next(), Some(Token::Id("x")));
        assert_eq!(iter.next(), Some(Token::Gives));
        assert_eq!(iter.next(), Some(Token::Id("x")));
        assert_eq!(iter.next(), None);
    }
}
