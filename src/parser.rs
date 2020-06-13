use std::{
    collections::HashMap,
    io::{self, BufRead, BufReader},
    fs::File,
};
use crate::{
    lexer::{self, Token, TokenIter},
    ast::{Ast, Expr},
    cmd::{self, Command},
};

/// Our hand-written parser.
/// Use with parse().
///
pub struct Parser {
    symbol_table: HashMap<String, Ast>,
    pause: bool,
    step: bool,
    count_steps: bool,
    non_interactive_mode: bool,
}

impl Parser {
    pub fn new() -> Parser {
        Parser {
            symbol_table: HashMap::new(),
            pause: false,
            step: true,
            count_steps: false,
            non_interactive_mode: false,
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
    /// assert_eq!(parser.parse("a b c d", None), parser.parse("(((a b) c) d)", None));
    /// ```
    ///
    /// - The lambda body stretches as far as possible:
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("lambda x . a b c", None), parser.parse("(lambda x . a b c)", None));
    /// ```
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("lambda x . a lambda y . y", None),
    ///     parser.parse("(lambda x . (a (lambda y . y)))", None));
    /// ```
    ///
    /// - Unnecessary parentheses are ignored:
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("((((a))))", None), parser.parse("a", None));
    /// ```
    ///
    /// Additionally,
    ///
    /// - Multiple variables may be put under a same lambda:
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("lambda x y z . x y", None),
    ///     parser.parse("lambda x . lambda y . lambda z . x y", None));
    /// ```
    ///
    ///
    /// - Lambda terms may be bound to symbols and later used.
    ///
    /// Note that the symbol substitution is lazy, meaning it is deferred until
    /// truly needed when perfoming a beta reduction:
    ///
    /// ```
    /// # use lambda_calc::{Parser, Ast, ast::Expr};
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("K = lambda x y . x", None), Ok(None));
    /// let redex = parser.parse("K a b", None).unwrap();
    /// // we haven't asked for any beta reduction, so K has not been
    /// // substituted yet
    /// let expected = Ast::new(Expr::Redex(
    ///     Box::new(Ast::new(Expr::Redex(
    ///         Box::new(Ast::new(Expr::Var { name: "K".to_string(), is_free: true })),
    ///         Box::new(Ast::new(Expr::Var { name: "a".to_string(), is_free: true })),
    ///     ))),
    ///     Box::new(Ast::new(Expr::Var { name: "b".to_string(), is_free: true })),
    /// )); // ((K a) b)
    /// assert_eq!(redex, Some(expected));
    /// let reduced = redex.unwrap().beta_reduce_quiet(&parser);
    /// let expected = Some(Ast::new(Expr::Var { name: "a".to_string(), is_free: true }));
    /// assert_eq!(reduced, expected);
    /// ```
    ///
    /// One must take care when binding an expression with free variables;
    /// because of the lazy substitution, these variables might misbehave when
    /// captured, e.g. in
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// let mut parser = Parser::new();
    /// assert_eq!(parser.parse("foo = \\f -> f x", None), Ok(None));
    /// let reduced = parser.parse("(\\x -> foo) a", None)
    ///     .unwrap()
    ///     .unwrap()
    ///     .beta_reduce_quiet(&parser);
    /// // the "x" in foo's definition is never replaced with "a",
    /// // because the definition is only substituted later
    /// let expected = parser.parse("foo", None)
    ///     .unwrap()
    ///     .unwrap()
    ///     .beta_reduce_quiet(&parser);
    /// assert_eq!(reduced, expected);
    /// ```
    ///

    pub fn parse(&mut self, line: &str, file_info: Option<String>) -> Result<Option<Ast>, String> {
        let token_iter = TokenIter::new(&line);
        {
            let mut new_token_iter = token_iter.clone();
            if let Some(Token::Command(cmd)) = new_token_iter.next() {
                self.run_command(cmd, new_token_iter.next());
                return Ok(None);
            }
        }
        LineParser::new(token_iter, file_info).parse(self)
    }

    /// Parse all lines in the file named filename, or stdin if filename is None.
    pub fn parse_file(&mut self, filename: Option<String>) -> Result<(), String> {
        match filename {
            None => {
                let stdin = io::stdin();
                let reader = stdin.lock();
                self.parse_file_with_reader(reader, "stdin")?;
            },
            Some(s) => {
                let file = match File::open(&s) {
                    Ok(file) => file,
                    Err(e) => return Err(e.to_string()),
                };
                let reader = BufReader::new(file);
                self.parse_file_with_reader(reader, &format!("file '{}'", s))?;
            },
        }
        Ok(())
    }

    fn parse_file_with_reader<R: BufRead>(&mut self,
                                          reader: R,
                                          file_info_prefix: &str) -> Result<(), String> {

        let mut line_num_beg = 0;
        let mut line_num_end;
        let mut lines = reader.lines();
        'read_expr: loop {
            let mut expr = match lines.next() {
                None => break 'read_expr,
                Some(line) => {
                    line_num_beg += 1;
                    match line {
                        Ok(l) => l,
                        Err(e) => return Err(e.to_string()),
                    }
                },
            };

            line_num_end = line_num_beg;

            while lexer::strip_whitespace_and_line_cont(&mut expr) {
                let line = match lines.next() {
                    None => return Err(format!("{}: line continuation not allowed in file's last line",
                                               file_info_prefix)),
                    Some(line) => {
                        line_num_end += 1;
                        match line {
                            Ok(l) => l,
                            Err(e) => return Err(e.to_string()),
                        }
                    }
                };
                expr.push_str(&line);
            }

            let file_info = if line_num_end > line_num_beg {
                format!("{}, lines {}-{}: ",
                        file_info_prefix, line_num_beg, line_num_end)
            } else {
                format!("{}, line {}: ", file_info_prefix, line_num_beg)
            };

            if let Some(ast) = self.parse(&expr, Some(file_info))? {
                if self.non_interactive_mode {
                    if let Some(ast) = ast.beta_reduce_quiet(&self) {
                        println!("{:#}", ast);
                    }
                }
            }

            line_num_beg = line_num_end;
        }
        Ok(())
    }

    /// Get an iterator for symbol names starting with prefix.
    /// May be used to implement TAB completion.
    pub fn get_symbol_names_with_prefix(&self, prefix: &str) -> Vec<&str> {
        self.symbol_table
            .keys()
            .filter(|s| s.starts_with(prefix))
            .map(|s| &s[..]) // convert &String to &str (though there might be a better way...)
            .collect()
    }

    /// Return an immutable reference to an expression if its name can be found
    /// in the symbol table.
    pub fn get_symbol(&self, name: &str) -> Option<&Ast> {
        self.symbol_table.get(name)
    }

    /// Insert a symbol and its corresponding expression into the symbol table.
    pub fn insert_symbol(&mut self, name: &str, ast: Ast) {
        self.symbol_table.insert(name.to_string(), ast);
    }

    /// Return whether pause mode is on or off.
    pub fn pause(&self) -> bool {
        self.pause
    }

    /// Return whether step mode is on or off.
    pub fn step(&self) -> bool {
        self.step
    }

    /// Return whether the count step mode is on or off.
    pub fn count_steps(&self) -> bool {
        self.count_steps
    }

    /// Turn on non-interactive mode.
    pub fn set_non_interactive_mode(&mut self) {
        self.non_interactive_mode = true;
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
                    if let Err(err) = self.parse_file(Some(filename.to_string())) {
                        eprintln!("error parsing file {}: '{}'", filename, err);
                    }
                },
                _ => panic!("lexer should have returned an Id as the argument to ':load'"),
            },
            Command::Define => panic!("Command::Define should never be returned by the lexer!"),
            Command::Pause => if !self.non_interactive_mode {
                handle_bool_cmd(&mut self.pause, arg);
            },
            Command::Step => handle_bool_cmd(&mut self.step, arg),
            Command::CountSteps => handle_bool_cmd(&mut self.count_steps, arg),
        }
    }
}

// used only for the current line of input, hence it won't own the symbol table
struct LineParser<'a, I>
    where I: Iterator<Item = Token<'a>> + Clone
{
    token_iter: I,
    file_info: Option<String>,
    lambda_vars: Vec<String>,
}

impl<'a, I> LineParser<'a, I>
    where I: Iterator<Item = Token<'a>> + Clone
{
    fn new(token_iter: I, file_info: Option<String>) -> LineParser<'a, I> {
        LineParser {
            token_iter,
            file_info,
            lambda_vars: Vec::new(),
        }
    }

    fn parse(&mut self, parser: &mut Parser) -> Result<Option<Ast>, String> {
        if let None = self.token_iter.clone().next() {
            return Ok(None); // empty line, ignore.
        }
        let is_def = self.check_is_def();
        self.sanity_checks(is_def)?;
        if is_def {
            self.parse_def(parser);
            Ok(None)
        } else {
            let ast = self.parse_ast(Vec::new())?;
            Ok(ast)
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
            Err(e) => self.print_syntax_err(&e),
            Ok(None) => self.print_syntax_err("a definition can't bind to an empty expression"),
            Ok(Some(ast)) => match ast.expr_ref() {
                Expr::LambdaTerm { .. } => {
                    parser.insert_symbol(name, ast);
                },
                Expr::Redex(_,_) => {
                    if let Some(non_redex) = ast.beta_reduce_quiet(parser) {
                        parser.insert_symbol(name, non_redex);
                    }
                },
                Expr::Var{name: var_name, is_free, } => {
                    assert!(is_free);
                    if let Some(ast) = parser.get_symbol(&var_name) {
                        let ast = ast.clone();
                        // bind to the symbol's definition directly
                        parser.insert_symbol(name, ast);
                    } else {
                        self.print_syntax_err("a definition can't bind to a single variable (unless it also has a definition)");
                    }
                }
            }
        }
    }

    // Our grammar is not LR(1) (and may not be context-free either),
    // so we parse by hand.
    fn parse_ast(&mut self, mut queue: Vec<Ast>) -> Result<Option<Ast>, String> {
        loop {
            match self.token_iter.next() {
                None | Some(Token::CloseParen) => {
                    return Ok(finalize_redex(queue));
                },
                Some(Token::OpenParen) => {
                    let ast = match self.parse_ast(Vec::new())? {
                        None => return Err("null expression after open paren".to_string()),
                        Some(x) => x,
                    };
                    queue.push(ast);
                },
                Some(Token::Id(s)) => {
                    let is_free = !self.lambda_vars.iter().any(|x| x == s);
                    queue.push(Ast::new(Expr::Var { name: s.to_string(), is_free, }));
                },
                Some(Token::Lambda) => {
                    let (ast, var_count) = self.parse_lambda(false)?;
                    queue.push(ast);
                    for _ in 0..var_count {
                        self.lambda_vars.pop();
                    }
                    return Ok(finalize_redex(queue));
                },
                Some(t) => return Err(format!("unexpected token '{:?}'", t)),
            }
        }
    }

    // This function expects that a lambda token has been immediately found,
    // or that there's an implicit lambda, for instance
    //  lambda x y -> x
    // which is treated as equivalent to
    //  lambda x -> (lambda y -> x)
    //
    // The number returned is the number of lambda variables pushed into
    // self.lambda_vars.
    //
    fn parse_lambda(&mut self, var_strict: bool) -> Result<(Ast, i32), String> {
        match self.token_iter.next() {
            Some(Token::Id(name)) => {
                if self.lambda_vars.iter().any(|x| x == name) {
                    return Err(format!("variable name '{}' is already in use by an inner lambda term", name));
                }
                self.lambda_vars.push(name.to_string());

                let (lambda_body, var_count) = self.parse_lambda(false)?;
                let ast = Ast::new(Expr::LambdaTerm {
                    var_name: name.to_string(),
                    var_strict,
                    body: Box::new(lambda_body),
                });

                Ok((ast, var_count + 1))
            },
            Some(Token::Strict) => {
                self.parse_lambda(true)
            },
            Some(Token::Gives) => {
                // finalize lambda term by returning its body.
                let ast = match self.parse_ast(Vec::new())? {
                    None => return Err("lambda term can't have empty body".to_string()),
                    Some(x) => x,
                };
                Ok((ast, 0))
            },
            Some(t) => Err(format!("token {:?} is not allowed in lambda term's head", t)),
            None => Err(format!("unfinished lambda term head")),
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

    fn sanity_checks(&self, is_def: bool) -> Result<(), String> {
        let mut paren_count:i32 = 0;
        let token_iter = self.token_iter.clone();

        for (i, token) in token_iter.enumerate() {
            match token {
                Token::Invalid(c) => {
                    return Err(self.prepend_file_info(format!("token {:?} is invalid", c)));
                },
                Token::OpenParen => paren_count += 1,
                Token::CloseParen => paren_count -= 1,
                Token::Def => {
                    if !is_def {
                        return Err(self.prepend_file_info(format!("wrong syntax for definition, should be <var> = <expr> (token {})", i)));
                    }
                },
                _ => {},
            }
        }
        if paren_count > 0 {
            return Err(self.prepend_file_info(format!("{} unclosed parentheses", paren_count)));
        } else if paren_count < 0 {
            return Err(self.prepend_file_info(format!("{} extra closing parentheses", -paren_count)));
        }
        Ok(())
    }

    fn prepend_file_info(&self, s: String) -> String {
        if let Some(fs) = &self.file_info {
            format!("{} {}", fs, s)
        } else {
            s
        }
    }

    fn print_syntax_err(&self, s: &str) {
        if let Some(fs) = &self.file_info {
            eprint!("{}", fs);
        }
        eprintln!("syntax error: {}", s);
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

fn handle_bool_cmd(val: &mut bool, arg: Option<Token>) {
    match arg {
        None => eprintln!("command requires an argument on|off|toggle"),
        Some(Token::Id(s)) => {
            if s == "on" {
                *val = true;
            } else if s == "off" {
                *val = false;
            } else if s == "toggle" {
                *val = !*val;
            } else {
                eprintln!("expected 'on', 'off' or 'toggle', found '{}'", s);
            }
        },
        _ => eprintln!("invalid argument: must be 'on', 'off' or 'toggle'"),
    }
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
    fn lambda_no_box(var_name: &str, var_strict: bool, body: Box<Ast>) -> Ast {
        Ast::new(Expr::LambdaTerm {
            var_name: var_name.to_string(),
            var_strict,
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
    fn lambda(var_name: &str, var_strict: bool, body: Box<Ast>) -> Box<Ast> {
        Box::new(lambda_no_box(var_name, var_strict, body))
    }
    fn redex(left: Box<Ast>, right: Box<Ast>) -> Box<Ast> {
        Box::new(redex_no_box(left, right))
    }

    #[test]
    fn empty_expr() {
        let mut parser = Parser::new();
        let expr = LineParser::new(vec![].into_iter(), None).parse(&mut parser);
        assert_eq!(Ok(None), expr);
    }

    // skeleton for non-empty expressions' tests (not definitions)
    fn expr_test<'a>(tokens: Vec<Token<'a>>, expected: Ast) {
        let mut parser = Parser::new();
        let ast = LineParser::new(tokens.into_iter(), None).parse(&mut parser);
        assert_eq!(Ok(Some(expected)), ast);
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
            lambda_no_box("x", false, bound_var("x"))
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
            lambda_no_box("x", false,
                          lambda("y", false,
                                 lambda("z", false, free_var("a"))))
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
            lambda_no_box("x", false, redex(bound_var("x"), free_var("a")))
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
                "x", false,
                lambda("y", false,
                       lambda("z", false,
                              redex(
                                  redex(bound_var("x"), bound_var("y")),
                                  bound_var("z")
                              ),
            )))
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
                "x", false,
                redex(
                    bound_var("x"),
                    lambda("y", false,
                           redex(
                               bound_var("x"),
                               lambda("z", false, bound_var("x"))
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
                lambda("x", false, bound_var("x"))
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
                    lambda("x", false, bound_var("x")),
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
                "x", false,
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
                lambda("x", false, bound_var("x")),
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
                    lambda("x", false,
                           lambda("y", false,
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
                    lambda("x", false, bound_var("x")),
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
                    lambda("x", false, bound_var("x")),
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
                        lambda("x", false, bound_var("x")),
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
                    lambda("x", false, bound_var("x")),
                    lambda("x", false, bound_var("x")),
                ),
                lambda("x", false, bound_var("x")),
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
                        lambda("x", false, bound_var("x")),
                    ),
                    free_var("b"),
                ),
                free_var("c"),
            ),
        );
    }

    #[test]
    fn bound_vars_inside_multiple_lambdas() {
        let tokens = vec![
            Token::Lambda, Token::Id("f"), Token::Gives,
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("f"),
            Token::CloseParen,
            Token::OpenParen,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("f"),
            Token::CloseParen,
        ]; // \f -> (\x -> f) (\x -> f)
        expr_test(
            tokens,
            lambda_no_box(
                "f", false,
                redex(
                    lambda("x", false, bound_var("f")),
                    lambda("x", false, bound_var("f")),
                ),
            ),
        );
    }

    #[test]
    fn single_strict_var_singlevar_lambda() {
        let tokens = vec![
            Token::Lambda, Token::Strict, Token::Id("x"),
            Token::Gives,
            Token::Id("x")
        ]; // \!x -> x
        expr_test(
            tokens,
            lambda_no_box("x", true, bound_var("x"))
        );
    }

    #[test]
    fn single_strict_var_multivar_lambda1() {
        let tokens = vec![
            Token::Lambda, Token::Strict, Token::Id("x"), Token::Id("y"),
            Token::Gives,
            Token::Id("x"), Token::Id("y")
        ]; // \!x y -> x y
        expr_test(
            tokens,
            lambda_no_box(
                "x", true,
                lambda(
                    "y", false,
                    redex(bound_var("x"), bound_var("y"))
                )
            )
        );
    }

    #[test]
    fn single_strict_var_multivar_lambda2() {
        let tokens = vec![
            Token::Lambda, Token::Id("x"), Token::Strict, Token::Id("y"),
            Token::Gives,
            Token::Id("x"), Token::Id("y")
        ]; // \x !y -> x y
        expr_test(
            tokens,
            lambda_no_box(
                "x", false,
                lambda(
                    "y", true,
                    redex(bound_var("x"), bound_var("y"))
                )
            )
        );
    }

    #[test]
    fn multi_strict_var_multivar_lambda() {
        let tokens = vec![
            Token::Lambda, Token::Strict, Token::Id("x"),
            Token::Id("y"),
            Token::Strict, Token::Id("z"),
            Token::Gives,
            Token::Id("z")
        ]; // \!x y !z -> z
        expr_test(
            tokens,
            lambda_no_box(
                "x", true,
                lambda(
                    "y", false,
                    lambda("z", true, bound_var("z"))
                )
            )
        );
    }

    #[test]
    fn insert_get_symbol() {
        let mut parser = Parser::new();
        let ast = lambda_no_box("x", false, bound_var("x"));
        parser.insert_symbol("I", ast.clone());
        assert_eq!(parser.get_symbol("I"), Some(&ast));
    }

    // for definition tests.
    fn def_test<'a>(name: &str, def_tokens: Vec<Token<'a>>, expected: Option<&Ast>) {
        let mut parser = Parser::new();
        assert_eq!(
            Ok(None),
            LineParser::new(def_tokens.into_iter(), None).parse(&mut parser)
        );
        let ast = parser.get_symbol(name);
        assert_eq!(expected, ast);
    }

    #[test]
    fn test_def_simple() {
        let def_tokens = vec![
            Token::Id("I"), Token::Def,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x")
        ];
        let expected = lambda_no_box("x", false, bound_var("x"));
        def_test("I", def_tokens, Some(&expected));
    }

    #[test]
    fn single_var_def_ignored() {
        let def_tokens = vec![
            Token::Id("x"), Token::Def, Token::Id("a")
        ];
        def_test("x", def_tokens, None);
    }

    #[test]
    fn symbol_alias() {
        let def1 = vec![
            Token::Id("f"), Token::Def,
            Token::Lambda, Token::Id("x"), Token::Gives, Token::Id("x"),
        ];
        let def2 = vec![
            Token::Id("g"), Token::Def, Token::Id("f"),
        ];
        let mut parser = Parser::new();
        assert_eq!(
            Ok(None),
            LineParser::new(def1.into_iter(), None).parse(&mut parser)
        );
        assert_eq!(
            Ok(None),
            LineParser::new(def2.into_iter(), None).parse(&mut parser)
        );
        assert_eq!(
            parser.get_symbol("g"),
            Some(&lambda_no_box("x", false, bound_var("x"))),
        );
    }
}
