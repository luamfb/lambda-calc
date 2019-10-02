use crate::lexer::{Token, TokenIter};
use crate::ast::{Var, Expr};
use std::collections::HashMap;

/// Our hand-written parser.
/// Use with parse().
///
pub struct Parser {
    symbol_table: HashMap<String, Expr>
}

impl Parser {
    pub fn new() -> Parser {
        Parser {
            symbol_table: HashMap::new(),
        }
    }

    // TODO so it turns out binary crates are not expected to have these
    // comments, so cargo test won't test them. We could just put them in a
    // man page but the tests wouldn't run and that ruins the whole thing.
    // We should probably migrate the majority of this code base to a library
    // crate instead (including this file)
    //
    /// Parse the string given in `line` and returns the corresponding Expr.
    /// Note that this function does not beta-reduce the expression.
    /// Left associativity is assumed by default:
    ///
    /// ```
    /// let parser = Parser::new();
    /// assert_eq!(parser.parse("a b c d"), parser.parse("(((a b) c) d)"));
    /// ```
    ///
    /// The lambda body stretches as far as possible:
    ///
    /// ```
    /// let parser = Parser::new();
    /// assert_eq!(parser.parse("lambda x . a b c"), parser.parse("(lambda x . a b c)"));
    /// ```
    ///
    /// ```
    /// let parser = Parser::new();
    /// assert_eq!(parser.parse("lambda x . a lambda y . y"),
    ///     parser.parse("(lambda x . a (lambda y . y))"));
    /// ```
    ///
    /// Unnecessary parentheses are ignored:
    ///
    /// ```
    /// let parser = Parser::new();
    /// assert_eq!(parser.parse("((((a))))"), parser.parse("a"));
    /// ```
    ///
    pub fn parse(&mut self, line: &str) -> Option<Expr> {
        let token_iter = TokenIter::new(&line);
        LineParser::new(token_iter).parse(&mut self.symbol_table)
    }
}


// used only for the current line of input, hence it won't own the symbol table
struct LineParser<'a, I>
    where I: Iterator<Item = Token<'a>> + Clone
{
    token_iter: I,
    // for the lambda terms currently in scope.
    // Note that the number stored here is the count of the variables inserted
    // up to the point the variable in question was inserted, so it's an
    // "inverse de Bruijin index" if you will.
    lambda_vars: HashMap<String, usize>,
}

impl<'a, I> LineParser<'a, I>
    where I: Iterator<Item = Token<'a>> + Clone
{
    fn new(token_iter: I) -> LineParser<'a, I> {
        LineParser {
            token_iter,
            lambda_vars: HashMap::new(),
        }
    }

    fn parse(&mut self, symbol_table: &mut HashMap<String, Expr>) -> Option<Expr> {
        if let None = self.token_iter.clone().next() {
            return None; // empty line, ignore.
        }
        let is_def = self.check_is_def();
        if !self.sanity_checks(is_def) {
            return None;
        }
        if is_def {
            self.parse_def(symbol_table);
            None
        } else {
            let mut expr = self.parse_expr(Vec::new())?;
            expr.substitute_symbols_from(symbol_table);
            Some(expr)
        }
    }

    fn parse_def(&mut self, symbol_table: &mut HashMap<String, Expr>) {
        let name = match self.token_iter.next() {
            Some(Token::Id(s)) => s,
            _ => panic!("expected definition, but 1st token is not an ID"),
        };
        match self.token_iter.next() {
            Some(Token::Def) => {},
            _ => panic!("expected definition, but 2nd token is not '=' or ':='"),
        }
        match self.parse_expr(Vec::new()) {
            None => eprintln!("a definition can't bind to an empty expression"),
            Some(mut expr) => match expr {
                Expr::LambdaTerm { var_name: _, body: _ } => {
                    expr.substitute_symbols_from(symbol_table);
                    symbol_table.insert(name.to_string(), expr);
                },
                Expr::Redex(_,_) => {
                    expr.substitute_symbols_from(symbol_table);
                    let non_redex = expr.beta_reduce_quiet();
                    symbol_table.insert(name.to_string(), non_redex);
                },
                Expr::Var(_) => {
                    eprintln!("a definition can't bind to a single variable");
                }
            }
        }
    }

    // Our grammar is not LR(1) (and may not be context-free either),
    // so we parse by hand.
    fn parse_expr(&mut self, mut queue: Vec<Expr>) -> Option<Expr> {
        loop {
            match self.token_iter.next() {
                None | Some(Token::CloseParen) => {
                    return finalize_redex(queue);
                },
                Some(Token::OpenParen) => {
                    queue.push(
                        self.parse_expr(Vec::new())
                        .expect("null expression after open paren")
                    );
                },
                Some(Token::Id(name)) => {
                    let cur_var = match self.lambda_vars.get(name) {
                        Some(i) => Var::BoundVar(self.lambda_vars.len() - i),
                        None => Var::FreeVar(name.to_string()),
                    };
                    queue.push(Expr::Var(cur_var));
                },
                Some(Token::Lambda) => {
                    queue.push(self.parse_lambda());
                    self.lambda_vars.clear();
                    return finalize_redex(queue);
                },
                t @ _ => {
                    panic!(format!(
                        "syntax error, token '{:?}'; should've been handled by sanity_checks()!",
                        t
                    ));
                },
            }
        }
    }

    // This function expects that a lambda token has been immediately found,
    // or that there's an implicit lambda, for instance
    //  lambda x y -> x
    // which is treated as equivalent to
    //  lambda x -> (lambda y -> x)
    //
    fn parse_lambda(&mut self) -> Expr {
        match self.token_iter.next() {
            Some(Token::Id(name)) => {
                if self.lambda_vars.contains_key(name) {
                    // ideally we should do something less drastic than panicking,
                    // e.g. returning None, but that could lead to a non-None
                    // inconsistent expression, which is even worse.
                    panic!("outer lambda variable cannot appear again as an inner lambda variable");
                }
                self.lambda_vars.insert(name.to_string(), self.lambda_vars.len());
                Expr::LambdaTerm {
                    var_name: name.to_string(),
                    body: Box::new(self.parse_lambda()),
                }
            },
            Some(Token::Gives) => {
                // finalize lambda term by returning its body.
                self.parse_expr(Vec::new())
                    .expect("lambda term can't have empty body")
            },
            _ => panic!("this token is not allowed in the head of a lambda term."),
        }
    }

    fn check_is_def(&self) -> bool {
        let mut token_iter = self.token_iter.clone();
        if let Some(Token::Id(_)) = token_iter.next() {
            if let Some(Token::Def) = token_iter.next() {
                return true;
            }
        }
        false
    }

    fn sanity_checks(&self, is_def: bool) -> bool {
        let mut paren_count:i32 = 0;
        let token_iter = self.token_iter.clone();

        for (i, token) in token_iter.enumerate() {
            match token {
                Token::Invalid => {
                    eprintln!("token number {} is invalid", i);
                    return false;
                },
                Token::OpenParen => paren_count += 1,
                Token::CloseParen => paren_count -= 1,
                Token::Def => {
                    if !is_def {
                        eprintln!(
                            "wrong syntax for definition, should be <var> = <expr> (token {})",
                            i
                        );
                        return false;
                    }
                },
                _ => {},
            }
        }
        if paren_count > 0 {
            eprintln!("{} unclosed parentheses", paren_count);
            return false;
        } else if paren_count < 0 {
            eprintln!("{} extra closing parentheses", -paren_count);
            return false;
        }
        true
    }
}

fn finalize_redex(mut queue: Vec<Expr>) -> Option<Expr> {
    let mut q_drain = queue.drain(..);

    let mut result = q_drain.next()?;
    for expr in q_drain {
        // left associative
        result = Expr::Redex(Box::new(result), Box::new(expr));
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_expr() {
        let mut symbol_table = HashMap::<String, Expr>::new();
        let expr = LineParser::new(vec![].into_iter()).parse(&mut symbol_table);
        assert_eq!(None, expr);
    }

    // skeleton for non-empty expressions' tests (not definitions)
    fn expr_test<'a>(tokens: Vec<Token<'a>>, expected: Expr) {
        let mut symbol_table = HashMap::<String, Expr>::new();
        let expr = LineParser::new(tokens.into_iter()).parse(&mut symbol_table);
        assert_eq!(Some(expected), expr);
    }

    #[test]
    fn single_free_var() {
        expr_test(
            vec![Token::Id("x")],
            Expr::Var(Var::FreeVar("x".to_string()))
        );
    }

    #[test]
    fn two_vars_redex() {
        expr_test(
            vec![Token::Id("x"), Token::Id("y")],
            Expr::Redex(
                Box::new(Expr::Var(Var::FreeVar("x".to_string()))),
                Box::new(Expr::Var(Var::FreeVar("y".to_string()))),
            )
        );
    }

    #[test]
    fn many_vars_redex() {
        let tokens = vec![
            Token::Id("x"), Token::Id("y"), Token::Id("z"), Token::Id("w")
        ]; // x y z w       -- should become (((x y) z) w)
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::FreeVar("x".to_string()))),
                        Box::new(Expr::Var(Var::FreeVar("y".to_string()))),
                    )),
                    Box::new(Expr::Var(Var::FreeVar("z".to_string()))),
                )),
                Box::new(Expr::Var(Var::FreeVar("w".to_string()))),
            )
        );
    }

    #[test]
    fn redex_left_paren() {
        // should give the same result as the unparenthesized version
        let tokens = vec![
            Token::OpenParen,
            Token::OpenParen,
            Token::Id("x"),
            Token::Id("y"),
            Token::CloseParen,
            Token::Id("z"),
            Token::CloseParen,
            Token::Id("w"),
        ]; // "((x y) z) w"

        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::FreeVar("x".to_string()))),
                        Box::new(Expr::Var(Var::FreeVar("y".to_string()))),
                    )),
                    Box::new(Expr::Var(Var::FreeVar("z".to_string()))),
                )),
                Box::new(Expr::Var(Var::FreeVar("w".to_string()))),
            )
        );
    }

    #[test]
    fn redex_right_paren() {
        let tokens = vec![
            Token::Id("x"),
            Token::OpenParen,
            Token::Id("y"),
            Token::Id("z"),
            Token::CloseParen,
        ]; // "x (y z)"
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Var(Var::FreeVar("x".to_string()))),
                Box::new(Expr::Redex(
                    Box::new(Expr::Var(Var::FreeVar("y".to_string()))),
                    Box::new(Expr::Var(Var::FreeVar("z".to_string()))),
                ))
            )
        );
    }

    #[test]
    fn simple_lambda_term() {
        let tokens = vec![
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
        ]; // lambda x . x
        expr_test(
            tokens,
            Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1)))
            }
        );
    }

    #[test]
    fn nested_lambdas() {
        let tokens = vec![
            Token::Lambda, Token::Id("x"), Token::Gives,
            Token::Lambda, Token::Id("y"), Token::Gives,
            Token::Lambda, Token::Id("z"), Token::Gives,
            Token::Id("a"),
        ]; // lambda x . lambda y . lambda z . a

        expr_test(
            tokens,
            Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "y".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "z".to_string(),
                        body: Box::new(Expr::Var(Var::FreeVar("a".to_string())))
                    })
                })
            }
        );
    }

    #[test]
    fn extra_parens() {
        let tokens = vec![
            Token::OpenParen,
            Token::OpenParen,
            Token::OpenParen,
            Token::Id("x"),
            Token::CloseParen,
            Token::CloseParen,
            Token::CloseParen,
        ]; // (((x)))
        expr_test(
            tokens,
            Expr::Var(Var::FreeVar("x".to_string()))
        );
    }

    #[test]
    fn free_var_bound_var() {
        let tokens = vec![
            Token::Lambda, Token::Id("x"), Token::Gives,
            Token::OpenParen,
            Token::Id("x"),
            Token::Id("a"),
            Token::CloseParen,
        ]; // lambda x . (x a)
        expr_test(
            tokens,
            Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::BoundVar(1))),
                        Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                ))
            }
        );
    }

    #[test]
    fn multi_var_lambda() {
        let tokens = vec![
            Token::Lambda,
            Token::Id("x"), Token::Id("y"), Token::Id("z"),
            Token::Gives,
            Token::OpenParen,
            Token::OpenParen,
            Token::Id("x"),
            Token::Id("y"),
            Token::CloseParen,
            Token::Id("z"),
            Token::CloseParen,
        ]; // lambda x y z . ((x y) z)
        expr_test(
            tokens,
            Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "y".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "z".to_string(),
                        body:
                            Box::new(Expr::Redex(
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var(Var::BoundVar(3))),
                                    Box::new(Expr::Var(Var::BoundVar(2))),
                                )),
                            Box::new(Expr::Var(Var::BoundVar(1))),
                        ))
                    })
                })
            }
        );
    }

    #[test]
    fn de_bruijn_index_update() {
        let tokens = vec![
            Token::Lambda, Token::Id("x"), Token::Gives,
            Token::OpenParen,
            Token::Id("x"),
            Token::OpenParen,
            Token::Lambda, Token::Id("y"), Token::Gives,
            Token::OpenParen,
            Token::Id("x"),
            Token::OpenParen,
            Token::Lambda, Token::Id("z"), Token::Gives,
            Token::Id("x"),
            Token::CloseParen,
            Token::CloseParen,
            Token::CloseParen,
            Token::CloseParen,
        ]; // lambda x . (x (lambda y . (x (lambda z . x))))

        expr_test(
            tokens,
            Expr::LambdaTerm {
                var_name: "x".to_string(),
                body:
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::BoundVar(1))),
                        Box::new(Expr::LambdaTerm {
                            var_name: "y".to_string(),
                            body:
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var(Var::BoundVar(2))),
                                    Box::new(Expr::LambdaTerm {
                                        var_name: "z".to_string(),
                                        body: Box::new(Expr::Var(Var::BoundVar(3))),
                                    })
                                ))
                        })
                    ))
            }
        );
    }

    #[test]
    fn lambda_without_paren_in_redex() {
        let tokens = vec![
            Token::Id("a"),
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x")
        ]; // a lambda x . x        -- should become (a (lambda x . x))
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::Var(Var::BoundVar(1))),
                })
            )
        );
    }

    #[test]
    fn left_paren_partial() {
        let tokens = vec![
            Token::OpenParen,
            Token::Id("a"),
            Token::Id("b"),
            Token::CloseParen,
            Token::Id("c"),
            Token::Id("d"),
        ]; // (a b) c d     -- should become (((a b) c) d)
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                        Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                    )),
                    Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
                )),
                Box::new(Expr::Var(Var::FreeVar("d".to_string()))),
            )
        );
    }

    #[test]
    fn right_paren_partial() {
        let tokens = vec![
            Token::Id("a"),
            Token::Id("b"),
            Token::OpenParen,
            Token::Id("c"),
            Token::Id("d"),
            Token::CloseParen,
        ]; // a b (c d)     -- should become ((a b) (c d))
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                    Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                )),
                Box::new(Expr::Redex(
                    Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
                    Box::new(Expr::Var(Var::FreeVar("d".to_string()))),
                )),
            )
        );
    }

    #[test]
    fn lambda_in_start_of_redex() {
        let tokens = vec![
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
            Token::Id("a"),
            Token::Id("b"),
        ]; // (lambda x . x) a b    -- should become (((lambda x . x) a) b)
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::LambdaTerm {
                        var_name: "x".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(1))),
                    }),
                    Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                )),
                Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
            )
        );
    }

    #[test]
    fn paren_middle1() {
        let tokens = vec![
            Token::Id("a"),
            Token::OpenParen,
            Token::Id("b"), Token::Id("c"),
            Token::CloseParen,
            Token::Id("d")
        ]; // a (b c) d         -- should become ((a (b c)) d)
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                        Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
                    ))
                )),
                Box::new(Expr::Var(Var::FreeVar("d".to_string()))),
            )
        );
    }

    #[test]
    fn paren_middle2() {
        let tokens = vec![
            Token::Id("a"), Token::Id("b"),
            Token::OpenParen,
            Token::Id("c"), Token::Id("d"),
            Token::CloseParen,
            Token::Id("e"),
            Token::Id("f"),
        ]; // a b (c d) e f       -- should become ((((a b) (c d)) e) f)
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Redex(
                            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                            Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                        )),
                        Box::new(Expr::Redex(
                            Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
                            Box::new(Expr::Var(Var::FreeVar("d".to_string()))),
                        )),
                    )),
                    Box::new(Expr::Var(Var::FreeVar("e".to_string()))),
                )),
                Box::new(Expr::Var(Var::FreeVar("f".to_string()))),
            )
        );
     }

    #[test]
    fn lambda_body_strecthes() {
        let tokens = vec![
            Token::Lambda, Token::Id("x"), Token::Gives,
            Token::Id("a"), Token::Id("b"), Token::Id("c"),
        ]; // lambda x . a b c
        expr_test(
            tokens,
            Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                        Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                    )),
                    Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
                ))
            }
        );
    }

    #[test]
    fn free_var_after_lambda() {
        let tokens = vec![
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
            Token::Id("x"),
        ]; // (lambda x . x) x
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::Var(Var::BoundVar(1))),
                }),
                Box::new(Expr::Var(Var::FreeVar("x".to_string()))),
            )
        );
    }

    #[test]
    fn free_vars_after_multivar_lambda() {
        let tokens = vec![
            Token::OpenParen,
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Id("y"), Token::Gives,
            Token::Id("x"),
            Token::Id("y"),
            Token::CloseParen,
            Token::Id("x"),
            Token::CloseParen,
            Token::Id("y"),
        ]; // ((lambda x y . x y) x) y
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::LambdaTerm {
                        var_name: "x".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "y".to_string(),
                            body: Box::new(Expr::Redex(
                                Box::new(Expr::Var(Var::BoundVar(2))),
                                Box::new(Expr::Var(Var::BoundVar(1))),
                            ))
                        })
                    }),
                    Box::new(Expr::Var(Var::FreeVar("x".to_string()))),
                )),
                Box::new(Expr::Var(Var::FreeVar("y".to_string()))),
            )
        );
    }

    #[test]
    fn lambda_middle() {
        let tokens = vec![
            Token::Id("a"),
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
            Token::Id("b"),
        ]; // a (lambda x . x) b
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                    Box::new(Expr::LambdaTerm {
                        var_name: "x".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(1))),
                    }),
                )),
                Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
            )
        );
    }

    #[test]
    fn redex_with_lambda_without_paren() {
        let tokens = vec![
            Token::OpenParen,
            Token::Id("a"),
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
            Token::Id("b"),
        ]; // (a lambda x . x) b
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                    Box::new(Expr::LambdaTerm {
                        var_name: "x".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(1))),
                    })
                )),
                Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
            )
        );
    }

    #[test]
    fn lambda_middle2() {
        let tokens = vec![
            Token::Id("a"),
            Token::Id("b"),
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
            Token::Id("c"),
            Token::Id("d"),
        ]; // a b (lambda x . x) c d    -- should become ((((a b) (lambda x . x)) c) d)
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Redex(
                            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                            Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                        )),
                        Box::new(Expr::LambdaTerm {
                            var_name: "x".to_string(),
                            body: Box::new(Expr::Var(Var::BoundVar(1))),
                        }),
                    )),
                    Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
                )),
                Box::new(Expr::Var(Var::FreeVar("d".to_string()))),
            )
        );
    }

    #[test]
    fn many_lambdas() {
        let tokens = vec![
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
        ]; // (lambda x . x) (lambda x . x) (lambda x . x)
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::LambdaTerm {
                        var_name: "x".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(1))),
                    }),
                    Box::new(Expr::LambdaTerm {
                        var_name: "x".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(1))),
                    }),
                )),
                Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::Var(Var::BoundVar(1))),
                }),
            )
        );
    }

    #[test]
    fn lambdas_right_assoc_redex() {
        let tokens = vec![
            Token::OpenParen,
            Token::OpenParen,
            Token::Id("a"),
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
            Token::Id("b"),
            Token::CloseParen,
            Token::Id("c"),
            Token::CloseParen,
        ]; // ((a (lambda x . x)) b) c
        expr_test(
            tokens,
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                        Box::new(Expr::LambdaTerm {
                            var_name: "x".to_string(),
                            body: Box::new(Expr::Var(Var::BoundVar(1))),
                        }),
                    )),
                    Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                )),
                Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
            )
        );
    }

    // for definition tests.
    fn def_test<'a>(def_tokens: Vec<Token<'a>>, tokens: Vec<Token<'a>>, expected: Expr) {
        let mut symbol_table = HashMap::<String, Expr>::new();
        assert_eq!(
            None,
            LineParser::new(def_tokens.into_iter()).parse(&mut symbol_table)
        );
        let expr = LineParser::new(tokens.into_iter()).parse(&mut symbol_table);
        assert_eq!(Some(expected), expr);
    }

    #[test]
    fn test_def_simple() {
        let def_tokens = vec![
            Token::Id("I"), Token::Def,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x")
        ];
        let tokens = vec![ Token::Id("I") ];
        let expected = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::Var(Var::BoundVar(1))),
        };
        def_test(def_tokens, tokens, expected);
    }

    #[test]
    fn single_var_def_ignored() {
        let def_tokens = vec![
            Token::Id("x"), Token::Def, Token::Id("a")
        ];
        let tokens = vec![ Token::Id("x") ];
        let expected = Expr::Var(Var::FreeVar("x".to_string()));
        def_test(def_tokens, tokens, expected);
    }

    #[test]
    fn def_replaced_in_free_lambda_var() {
        let def_tokens = vec![
            Token::Id("I"), Token::Def,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x")
        ];
        let tokens = vec![
            Token::Lambda, Token::Id("y"), Token::Gives,
            Token::Id("I"), Token::Id("y"),
        ];
        let expected = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::Var(Var::BoundVar(1))),
                }),
                Box::new(Expr::Var(Var::BoundVar(1))),
            )),
        }; // lambda y . (lambda x . x) y
        def_test(def_tokens, tokens, expected);
    }

    #[test]
    fn def_not_replaced_in_bound_var() {
        let def_tokens = vec![
            Token::Id("a"), Token::Def,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x")
        ];
        let tokens = vec![
            Token::Lambda, Token::Id("a"), Token::Gives, Token::Id("a")
        ];
        let expected = Expr::LambdaTerm {
            var_name: "a".to_string(),
            body: Box::new(Expr::Var(Var::BoundVar(1))),
        };
        def_test(def_tokens, tokens, expected);
    }

    #[test]
    fn def_replaced_redex() {
        let def_tokens = vec![
            Token::Id("I"), Token::Def,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x")
        ];

        let tokens = vec![
            Token::Id("I"), Token::Id("I")
        ];
        let expected = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            })
        );
        def_test(def_tokens, tokens, expected);
    }

    #[test]
    fn def_with_redex() {
        let def_tokens = vec![
            Token::Id("a"), Token::Def,
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
            Token::CloseParen,
            Token::Lambda, Token::Id("y"), Token::Gives, Token::Id("y"),
        ];
        let tokens = vec![ Token::Id("a") ];
        let expected = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::Var(Var::BoundVar(1))),
        };
        def_test(def_tokens, tokens, expected);
    }

    #[test]
    fn multilevel_def() {
        let def1_tokens = vec![
            Token::Id("a"), Token::Def,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
        ]; // a = lambda x . x
        let def2_tokens = vec![
            Token::Id("b"), Token::Def,
            Token::Lambda, Token::Id("y"), Token::Gives, Token::Id("a"),
        ]; // b = lambda y . a
        let tokens = vec![ Token::Id("b") ];

        let mut symbol_table = HashMap::<String, Expr>::new();
        assert_eq!(
            LineParser::new(def1_tokens.into_iter()).parse(&mut symbol_table),
            None
        );
        assert_eq!(
            LineParser::new(def2_tokens.into_iter()).parse(&mut symbol_table),
            None
        );
        let expr = LineParser::new(tokens.into_iter()).parse(&mut symbol_table);
        assert_eq!(
            Some(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::Var(Var::BoundVar(1))),
                }),
            }),
            expr
        );
    }
}
