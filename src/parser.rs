use crate::{
    lexer::{Token, TokenIter},
    ast::{Ast, Expr},
    cmd,
    cmd::Command,
};
use std::{
    collections::{HashSet, HashMap},
    io::{BufRead, BufReader},
    fs::File,
};

/// Our hand-written parser.
/// Use with parse().
///
pub struct Parser {
    symbol_table: HashMap<String, Ast>,
}

impl Parser {
    pub fn new() -> Parser {
        Parser {
            symbol_table: HashMap::new(),
        }
    }

    /// Parse the string given in `line` and returns the corresponding Ast.
    /// Note that this function does not beta-reduce the expression.
    ///
    /// This parser uses all usual rules for implicit parenthesization in
    /// lambda calculus, namely:
    ///
    /// - Left associativity is assumed by default:
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("a b c d"), parser.parse("(((a b) c) d)"));
    /// ```
    ///
    /// - The lambda body stretches as far as possible:
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("lambda x . a b c"), parser.parse("(lambda x . a b c)"));
    /// ```
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("lambda x . a lambda y . y"),
    ///     parser.parse("(lambda x . (a (lambda y . y)))"));
    /// ```
    ///
    /// - Unnecessary parentheses are ignored:
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("((((a))))"), parser.parse("a"));
    /// ```
    ///
    /// Additionally,
    ///
    /// - Multiple variables may be put under a same lambda:
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("lambda x y z . x y"),
    ///     parser.parse("lambda x . lambda y . lambda z . x y"));
    /// ```
    ///
    ///
    /// - Lambda terms may be bound to symbols and later used:
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("K = lambda x y . x"), None);
    /// assert_eq!(parser.parse("I = lambda x . x"), None);
    /// assert_eq!(parser.parse("K I"),
    ///     parser.parse("(lambda x y . x) (lambda x . x)"));
    /// ```
    ///
    pub fn parse(&mut self, line: &str) -> Option<Ast> {
        let token_iter = TokenIter::new(&line);
        {
            let mut new_token_iter = token_iter.clone();
            if let Some(Token::Command(cmd)) = new_token_iter.next() {
                self.run_command(cmd, new_token_iter.next());
                return None;
            }
        }
        LineParser::new(token_iter).parse(self)
    }

    /// Parse all lines in filename.
    pub fn parse_file(&mut self, filename: &str) -> std::io::Result<()> {
        let reader = BufReader::new(File::open(filename)?);
        for line in reader.lines() {
            self.parse(&line?);
        }
        Ok(())
    }

    /// Return an immutable reference to an expression if its name can be found
    /// in the symbol table.
    pub fn get_symbol(&self, name: &str) -> Option<&Ast> {
        self.symbol_table.get(name)
    }

    pub fn insert_symbol(&mut self, name: &str, ast: Ast) {
        self.symbol_table.insert(name.to_string(), ast);
    }

    fn run_command(&mut self, cmd: Command, arg: Option<Token>) {
        match cmd {
            Command::Help => {
                cmd::print_usage();
            },
            Command::Load => match arg {
                None => {
                    eprintln!("':load' requires a filename");
                    return;
                },
                Some(Token::Id(filename)) => {
                    if let Err(err) = self.parse_file(filename) {
                        eprintln!("error parsing file {}: '{}'", filename, err);
                    }
                },
                _ => panic!("lexer should have returned an Id as the argument to ':load'"),
            },
            Command::Define => panic!("Command::Define should never be returned by the lexer!"),
        }
    }
}

// used only for the current line of input, hence it won't own the symbol table
struct LineParser<'a, I>
    where I: Iterator<Item = Token<'a>> + Clone
{
    token_iter: I,
    lambda_vars: HashSet<String>,
}

impl<'a, I> LineParser<'a, I>
    where I: Iterator<Item = Token<'a>> + Clone
{
    fn new(token_iter: I) -> LineParser<'a, I> {
        LineParser {
            token_iter,
            lambda_vars: HashSet::new(),
        }
    }

    fn parse(&mut self, parser: &mut Parser) -> Option<Ast> {
        if let None = self.token_iter.clone().next() {
            return None; // empty line, ignore.
        }
        let is_def = self.check_is_def();
        if !self.sanity_checks(is_def) {
            return None;
        }
        if is_def {
            self.parse_def(parser);
            None
        } else {
            let ast = self.parse_ast(Vec::new())?;
            Some(ast)
        }
    }

    fn parse_def(&mut self, parser: &mut Parser) {
        let name = match self.token_iter.next() {
            Some(Token::Id(s)) => s,
            _ => panic!("expected definition, but 1st token is not an ID"),
        };
        match self.token_iter.next() {
            Some(Token::Def) => {},
            _ => panic!("expected definition, but 2nd token is not '=' or ':='"),
        }
        match self.parse_ast(Vec::new()) {
            None => eprintln!("a definition can't bind to an empty expression"),
            Some(ast) => match ast.expr_ref() {
                Expr::LambdaTerm { var_name: _, body: _ } => {
                    parser.insert_symbol(name,  ast);
                },
                Expr::Redex(_,_) => {
                    let non_redex = ast.beta_reduce_quiet(parser);
                    parser.insert_symbol(name, non_redex);
                },
                Expr::Var{name: _, is_free: _} => {
                    eprintln!("a definition can't bind to a single variable");
                }
            }
        }
    }

    // Our grammar is not LR(1) (and may not be context-free either),
    // so we parse by hand.
    fn parse_ast(&mut self, mut queue: Vec<Ast>) -> Option<Ast> {
        loop {
            match self.token_iter.next() {
                None | Some(Token::CloseParen) => {
                    return finalize_redex(queue);
                },
                Some(Token::OpenParen) => {
                    queue.push(
                        self.parse_ast(Vec::new())
                        .expect("null expression after open paren")
                    );
                },
                Some(Token::Id(s)) => {
                    let is_free = !self.lambda_vars.contains(s);
                    queue.push(Ast::new(Expr::Var { name: s.to_string(), is_free, }));
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
    fn parse_lambda(&mut self) -> Ast {
        match self.token_iter.next() {
            Some(Token::Id(name)) => {
                if self.lambda_vars.contains(name) {
                    // Ideally we should do something less drastic than panicking,
                    // e.g. returning None, but that could lead to a non-None
                    // inconsistent expression, which is even worse.
                    //
                    panic!("outer lambda variable cannot appear again as an inner lambda variable");
                }
                self.lambda_vars.insert(name.to_string());
                Ast::new(Expr::LambdaTerm {
                    var_name: name.to_string(),
                    body: Box::new(self.parse_lambda()),
                })
            },
            Some(Token::Gives) => {
                // finalize lambda term by returning its body.
                self.parse_ast(Vec::new())
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

fn finalize_redex(mut queue: Vec<Ast>) -> Option<Ast> {
    let mut q_drain = queue.drain(..);

    let mut result = q_drain.next()?;
    for expr in q_drain {
        // left associative
        result = Ast::new(Expr::Redex(Box::new(result), Box::new(expr)));
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    // wrappers to reduce boilerplate.
    fn free_var_no_box(name: &str) -> Ast {
        Ast::new(Expr::Var {
            name: name.to_string(),
            is_free: true,
        })
    }
    fn bound_var_no_box(name: &str) -> Ast {
        Ast::new(Expr::Var {
            name: name.to_string(),
            is_free: false,
        })
    }
    fn lambda_no_box(var_name: &str, body: Box<Ast>) -> Ast {
        Ast::new(Expr::LambdaTerm {
            var_name: var_name.to_string(),
            body,
        })
    }
    fn redex_no_box(left: Box<Ast>, right: Box<Ast>) -> Ast {
        Ast::new(Expr::Redex(
            left,
            right,
        ))
    }
    fn free_var(name: &str) -> Box<Ast> {
        Box::new(free_var_no_box(name))
    }
    fn bound_var(name: &str) -> Box<Ast> {
        Box::new(bound_var_no_box(name))
    }
    fn lambda(var_name: &str, body: Box<Ast>) -> Box<Ast> {
        Box::new(lambda_no_box(var_name, body))
    }
    fn redex(left: Box<Ast>, right: Box<Ast>) -> Box<Ast> {
        Box::new(redex_no_box(left, right))
    }

    #[test]
    fn empty_expr() {
        let mut parser = Parser::new();
        let expr = LineParser::new(vec![].into_iter()).parse(&mut parser);
        assert_eq!(None, expr);
    }

    // skeleton for non-empty expressions' tests (not definitions)
    fn expr_test<'a>(tokens: Vec<Token<'a>>, expected: Ast) {
        let mut parser = Parser::new();
        let ast = LineParser::new(tokens.into_iter()).parse(&mut parser);
        assert_eq!(Some(expected), ast);
    }

    #[test]
    fn single_free_var() {
        expr_test(
            vec![Token::Id("x")],
            free_var_no_box("x")
        );
    }

    #[test]
    fn two_vars_redex() {
        expr_test(
            vec![Token::Id("x"), Token::Id("y")],
            redex_no_box(free_var("x"), free_var("y"))
        );
    }

    #[test]
    fn many_vars_redex() {
        let tokens = vec![
            Token::Id("x"), Token::Id("y"), Token::Id("z"), Token::Id("w")
        ]; // x y z w       -- should become (((x y) z) w)
        expr_test(
            tokens,
            /*
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var{ name: "x".to_string(), is_free: true }),
                        Box::new(Expr::Var{ name: "y".to_string(), is_free: true }),
                    )),
                    Box::new(Expr::Var{ name: "z".to_string(), is_free: true }),
                )),
                Box::new(Expr::Var{ name: "w".to_string(), is_free: true }),
            )
            */
            redex_no_box(
                redex(
                    redex(free_var("x"), free_var("y")),
                    free_var("z"),
                ),
                free_var("w"),
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
            /*
            Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var{ name: "x".to_string(), is_free: true }),
                        Box::new(Expr::Var{ name: "y".to_string(), is_free: true }),
                    )),
                    Box::new(Expr::Var{ name: "z".to_string(), is_free: true }),
                )),
                Box::new(Expr::Var{ name: "w".to_string(), is_free: true }),
            )
            */
            redex_no_box(
                redex(
                    redex(free_var("x"), free_var("y")),
                    free_var("z"),
                ),
                free_var("w"),
            ),
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
            redex_no_box(
                free_var("x"),
                redex(
                    free_var("y"),
                    free_var("z"),
                ),
            ),
        );
    }

    #[test]
    fn simple_lambda_term() {
        let tokens = vec![
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
        ]; // lambda x . x
        expr_test(
            tokens,
            lambda_no_box("x", bound_var("x"))
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
            lambda_no_box("x", lambda("y", lambda("z", free_var("a"))))
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
            free_var_no_box("x"),
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
            /*
            Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Redex(
                        Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                        Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
                ))
            }
            */
            lambda_no_box("x", redex(bound_var("x"), free_var("a")))
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
            lambda_no_box(
                "x",
                lambda("y",
                       lambda("z",
                              redex(
                                  redex(bound_var("x"), bound_var("y")),
                                  bound_var("z")
                              ),
            )))
            /*
            Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "y".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "z".to_string(),
                        body:
                            Box::new(Expr::Redex(
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                                    Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
                                )),
                            Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                        ))
                    })
                })
            }
            */
        );
    }

    #[test]
    fn multi_var_lambda2() {
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
            lambda_no_box(
                "x",
                redex(
                    bound_var("x"),
                    lambda("y",
                           redex(
                               bound_var("x"),
                               lambda("z", bound_var("x"))
                           )
                    )
                )
            ),
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
            redex_no_box(
                free_var("a"),
                lambda("x", bound_var("x"))
            ),
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
            redex_no_box(
                redex(
                    redex(free_var("a"), free_var("b")),
                    free_var("c")
                ),
                free_var("d")
            ),
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
            redex_no_box(
                redex(free_var("a"), free_var("b")),
                redex(free_var("c"), free_var("d")),
            ),
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
            redex_no_box(
                redex(
                    lambda("x", bound_var("x")),
                    free_var("a"),
                ),
                free_var("b"),
            ),
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
            redex_no_box(
                redex(
                    free_var("a"),
                    redex(
                        free_var("b"),
                        free_var("c"),
                    ),
                ),
                free_var("d"),
            ),
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
            redex_no_box(
                redex(
                    redex(
                        redex(free_var("a"), free_var("b")),
                        redex(free_var("c"), free_var("d")),
                    ),
                    free_var("e"),
                ),
                free_var("f"),
            ),
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
            lambda_no_box(
                "x",
                redex(
                    redex(free_var("a"), free_var("b")),
                    free_var("c")
                ),
            ),
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
            redex_no_box(
                lambda("x", bound_var("x")),
                free_var("x")
            ),
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
            redex_no_box(
                redex(
                    lambda("x",
                           lambda("y",
                                  redex(bound_var("x"), bound_var("y"))
                           )
                    ),
                    free_var("x"),
                ),
                free_var("y"),
            ),
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
            redex_no_box(
                redex(
                    free_var("a"),
                    lambda("x", bound_var("x")),
                ),
                free_var("b")
            ),
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
            redex_no_box(
                redex(
                    free_var("a"),
                    lambda("x", bound_var("x")),
                ),
                free_var("b"),
            ),
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
            redex_no_box(
                redex(
                    redex(
                        redex(free_var("a"), free_var("b")),
                        lambda("x", bound_var("x")),
                    ),
                    free_var("c"),
                ),
                free_var("d"),
            ),
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
            redex_no_box(
                redex(
                    lambda("x", bound_var("x")),
                    lambda("x", bound_var("x")),
                ),
                lambda("x", bound_var("x")),
            ),
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
            redex_no_box(
                redex(
                    redex(
                        free_var("a"),
                        lambda("x", bound_var("x")),
                    ),
                    free_var("b"),
                ),
                free_var("c"),
            ),
        );
    }

    // for definition tests.
    fn def_test<'a>(def_tokens: Vec<Token<'a>>, tokens: Vec<Token<'a>>, expected: Ast) {
        let mut parser = Parser::new();
        assert_eq!(
            None,
            LineParser::new(def_tokens.into_iter()).parse(&mut parser)
        );
        let ast = LineParser::new(tokens.into_iter()).parse(&mut parser);
        assert_eq!(Some(expected), ast);
    }

    #[test]
    fn test_def_simple() {
        let def_tokens = vec![
            Token::Id("I"), Token::Def,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x")
        ];
        let tokens = vec![ Token::Id("I") ];
        let expected = lambda_no_box("x", bound_var("x"));
        def_test(def_tokens, tokens, expected);
    }

    #[test]
    fn single_var_def_ignored() {
        let def_tokens = vec![
            Token::Id("x"), Token::Def, Token::Id("a")
        ];
        let tokens = vec![ Token::Id("x") ];
        let expected = free_var_no_box("x");
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
        let expected = lambda_no_box(
            "y",
            redex(
                lambda("x",
                       bound_var("x"),
                ),
                bound_var("y"),
            ),
        );
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
        let expected = lambda_no_box("a", bound_var("a"));
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
        let expected = redex_no_box(
            lambda("x", bound_var("x")),
            lambda("x", bound_var("x")),
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
        let expected = lambda_no_box("y", bound_var("y"));
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

        let mut parser = Parser::new();
        assert_eq!(
            LineParser::new(def1_tokens.into_iter()).parse(&mut parser),
            None
        );
        assert_eq!(
            LineParser::new(def2_tokens.into_iter()).parse(&mut parser),
            None
        );
        let expr = LineParser::new(tokens.into_iter()).parse(&mut parser);
        assert_eq!(
            Some(lambda_no_box("y", lambda("x", bound_var("x")))),
            expr
        );
    }

    #[test]
    fn alpha_conversion_def() {
        let def_tokens = vec![
            Token::Id("id"), Token::Def,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
        ];
        let tokens = vec![
            Token::Lambda, Token::Id("x"), Token::Gives,
            Token::Id("x"), Token::Id("id"),
        ];
        let expected = lambda_no_box(
            "x",
            redex(
                bound_var("x"),
                lambda("x'", bound_var("x'")),
            ),
        );
        def_test(def_tokens, tokens, expected);

    }
}
