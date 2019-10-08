#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<'a> {
    Invalid,
    Id(&'a str),
    Def,
    Gives,
    Lambda,
    OpenParen,
    CloseParen,
}

#[derive(Clone)]
pub struct TokenIter<'a> {
    s: &'a str,
    pos: usize,
}

impl<'a> Iterator for TokenIter<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Token<'a>> {
        self.consume_whitespace();

        let rest_of_string = self.rest_of_string();
        if rest_of_string.is_empty() {
            return None;
        }

        // The order matters in those lists: if one token is prefix of another,
        // the largest one must come first.
        //
        let classifier = &[
            (vec!["=>", "->", "."],     Token::Gives),
            (vec!["=", ":="],           Token::Def),
            (vec!["λ", "\\", "lambda"], Token::Lambda),
            (vec!["("],                 Token::OpenParen),
            (vec![")"],                 Token::CloseParen),
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

        let (name_len, last_char_len) = self.get_next_word_and_last_char_len();

        if name_len == 0 {
            // we must increment position here too, otherwise we'll yield
            // the same invalid token forever.
            // Note that each invalid token we yield has 1 char only.
            //
            self.pos += last_char_len;
            Token::Invalid
        } else {
            self.pos += name_len;
            Token::Id(&rest_of_string[0..name_len])
        }
    }

    fn get_next_word_and_last_char_len(&self) -> (usize, usize) {
        let rest_of_string = self.rest_of_string();
        let mut name_len = 0;
        let mut last_char_len = 0;

        for c in rest_of_string.chars() {
            last_char_len = c.len_utf8();
            if !c.is_alphanumeric() && c != '_' {
                break
            }
            name_len += last_char_len;
        }
        (name_len, last_char_len)
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
}
