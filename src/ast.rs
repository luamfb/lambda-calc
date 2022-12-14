use std::{
    fmt::{self, Display, Formatter},
    collections::{HashMap, HashSet},
    io::Read,
};

use signal_hook::{
    iterator::Signals,
    SIGINT,
};

use crate::parser::Parser;

/// The abstract syntax tree constructed from the lambda expression.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Ast {
    expr: Expr,
    reduced_last: bool,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expr {
    Var { name: String, is_free: bool, },
    LambdaTerm {var_name: String, var_strict: bool, body: Box<Ast>},
    Redex(Box<Ast>, Box<Ast>),
}

impl Ast {
    pub fn new(expr: Expr) -> Ast {
        Ast {
            expr,
            reduced_last: false,
        }
    }

    /// Get an un-mutable reference to the underlying expression.
    pub fn expr_ref(&self) -> &Expr {
        &self.expr
    }

    /// Applies beta reductions until it's no longer possible, printing
    /// the result after each round of beta reduction.
    ///
    /// Uses normal order reduction strategy (leftmost outermost redex first),
    /// otherwise certain reductions would loop infintely:
    ///
    /// ```
    /// # use lambda_calc::Parser;
    /// # use lambda_calc::Ast;
    /// # use lambda_calc::ast::Expr;
    /// let mut parser = Parser::new();
    /// let redex = parser
    ///     .parse("(lambda x . a) ((lambda y . y y) (lambda y . y y))", None)
    ///     .unwrap()
    ///     .unwrap();
    /// let non_redex = redex.beta_reduce_print(&parser);
    /// assert_eq!(non_redex, Some(Ast::new(Expr::Var{name: "a".to_string(), is_free: true})));
    /// ```
    ///
    /// This function does not attempt to predict infinite loops.
    pub fn beta_reduce_print(self, parser: &Parser) -> Option<Ast> {
        self.beta_reduce(parser, true)
    }

    /// Identical to beta_reduce_print() but doesn't print anything.
    pub fn beta_reduce_quiet(self, parser: &Parser) -> Option<Ast> {
        self.beta_reduce(parser, false)
    }

    /// Returns None if interrupted (with CTRL-C)
    fn beta_reduce(mut self, parser: &Parser, should_print: bool) -> Option<Ast> {
        let last_step_changed;
        let mut printed_once = false;
        let mut num_steps = 0;

        let signals = match Signals::new(&[SIGINT]) {
            Ok(sig) => Some(sig),
            Err(e) => {
                eprintln!("failed to register SIGINT hook: {}", e);
                None
            },
        };

        loop {
            let pair = self.beta_reduce_once(&mut HashSet::new(), parser);
            self = pair.0;
            let expr_has_changed = pair.1;
            if !expr_has_changed {
                let (ast, expr_has_changed) = self.last_step_beta_reduce(&parser);
                self = ast;
                last_step_changed = expr_has_changed;
                break;
            }
            num_steps += 1;
            if should_print && parser.step() {
                println!("= {}", self);
                printed_once = true;
                if parser.pause() {
                    ::std::io::stdin()
                        .lock()
                        .bytes()
                        .skip_while(
                            // Probably not portable; can't find a better way to do this.
                            // Discard all characters until newline is found.
                            |x| *x.as_ref().expect("failed to read from stdin") != 0xA
                        ).next();
                }
            }
            if let Some(ref sig) = signals {
                for signal in sig.pending() {
                    if signal == SIGINT {
                        return None;
                    }
                }
            }
        }
        if should_print && (!printed_once || last_step_changed) {
            println!("= {}", self);
        }
        if last_step_changed {
            num_steps += 1;
        }
        if should_print && parser.count_steps() {
            println!("{} reduction steps", num_steps);
        }
        Some(self)
    }

    // This function is due to a corner case: if the entire expression
    // is a free variable, look it up from the symbol table.
    //
    fn last_step_beta_reduce(self, parser: &Parser) -> (Ast, bool) {
        match self.expr {
            Expr::Var { name, is_free: true } => {
                if let Some(ast) = parser.get_symbol(&name) {
                    let mut new_ast = ast.clone();
                    new_ast.reduced_last = true;
                    (new_ast, true)
                } else {
                    // reconstruct variable
                    (Ast::new(Expr::Var { name, is_free: true }), false)
                }
            },
            _ => (self, false)
        }
    }

    fn beta_reduce_once(mut self,
                        lambda_vars_in_use: &mut HashSet<String>,
                        parser: &Parser) -> (Ast, bool) {
        self.unset_reduced_last();
        self.beta_reduce_once_recur(lambda_vars_in_use, parser)
    }

    fn unset_reduced_last(&mut self) {
        self.reduced_last = false;
        match &mut self.expr {
            Expr::Redex(left, right) => {
                left.unset_reduced_last();
                right.unset_reduced_last();
            },
            Expr::LambdaTerm { var_name: _, var_strict: _, body, } => {
                body.unset_reduced_last();
            },
            _ => {},
        }
    }

    fn beta_reduce_redex_recur(left: Box<Ast>,
                               right: Box<Ast>,
                               lambda_vars_in_use: &mut HashSet<String>,
                               parser: &Parser) -> (Ast, bool) {
        let (new_left, has_changed)
            = left.beta_reduce_once_recur(lambda_vars_in_use, parser);
        if has_changed {
            let new_ast = Ast::new(Expr::Redex(Box::new(new_left), right));
            return (new_ast, true);
        }
        let (new_right, has_changed)
            = right.beta_reduce_once_recur(lambda_vars_in_use, parser);
        let new_ast = Ast::new(Expr::Redex(
            Box::new(new_left),
            Box::new(new_right)
        ));
        (new_ast, has_changed)
    }

    // Returns the expression after attemtping to apply a single beta-reduction,
    // and a boolean which is whether or not a reduction could be made.
    // Call unset_reduced_last() before this.
    //
    fn beta_reduce_once_recur(self,
                              lambda_vars_in_use: &mut HashSet<String>,
                              parser: &Parser) -> (Ast, bool) {
        match self.expr {
            Expr::Redex(left, mut right) => {
                match left.expr {
                    Expr::LambdaTerm {var_name, var_strict, body: mut lambda_body} => {
                        // if the variable is marked as strict, try to eagerly
                        // evaluate its argument before replacing
                        //
                        if var_strict {
                            let (new_right, has_changed) =
                                right.beta_reduce_once_recur(&mut HashSet::new(), parser);
                            *right = new_right;
                            if has_changed {
                                let redex = Ast::strict_var_reconstruct_redex(
                                    var_name,
                                    var_strict,
                                    lambda_body,
                                    right);
                                return (redex, true);
                            } else {
                                let (new_right, has_changed) =
                                    right.last_step_beta_reduce(&parser);
                                *right = new_right;
                                if has_changed {
                                    let redex = Ast::strict_var_reconstruct_redex(
                                        var_name,
                                        var_strict,
                                        lambda_body,
                                        right);
                                    return (redex, true);
                                }
                            }
                        }
                        // note that we don't include this lambda's var name in
                        // lambda_vars_in_use, since it's the variable that will
                        // be replaced by reduction
                        //
                        lambda_body.get_all_lambda_vars(lambda_vars_in_use);
                        // we also get the lambda variables in the left side,
                        // because, if we have
                        //      (\y x -> y x) (\x x1 -> x x1)
                        // the right hand side x should be converted to x2
                        // rather than x1.
                        //
                        let mut lambda_vars_right = HashSet::new();
                        right.get_all_lambda_vars(&mut lambda_vars_right);

                        right.alpha_convert(lambda_vars_in_use,
                                            &lambda_vars_right,
                                            &mut HashMap::new());
                        lambda_body.replace_bound_var(&right, &var_name, lambda_vars_in_use);

                        lambda_vars_in_use.clear();

                        let new_ast = *lambda_body;
                        (new_ast, true)
                    },
                    Expr::Var { name, is_free:true } => {
                        // if it's a free variable, try to find its name in the
                        // symbol table
                        if let Some(ast_ref) = parser.get_symbol(&name) {
                            let mut new_left = ast_ref.clone();

                            let mut lambda_vars_right = HashSet::new();
                            new_left.get_all_lambda_vars(&mut lambda_vars_right);

                            new_left.alpha_convert(lambda_vars_in_use,
                                                   &lambda_vars_right,
                                                   &mut HashMap::new());
                            new_left.reduced_last = true;
                            let new_ast = Ast::new(Expr::Redex(
                                Box::new(new_left),
                                right,
                            ));
                            (new_ast, true)
                        } else {
                            let new_left = Box::new(Ast::new(Expr::Var {
                                name,
                                is_free: true,
                            }));
                            Ast::beta_reduce_redex_recur(new_left, right, lambda_vars_in_use, parser)
                        }
                    },
                    _ => {
                        Ast::beta_reduce_redex_recur(left, right, lambda_vars_in_use, parser)
                    }
                }
            },
            Expr::LambdaTerm {var_name, var_strict, body: lambda_body} => {
                lambda_vars_in_use.insert(var_name.clone());

                let (new_body, has_changed)
                    = lambda_body.beta_reduce_once_recur(lambda_vars_in_use, parser);

                //lambda_vars_in_use.remove(&name);

                let new_lambda = Ast::new(Expr::LambdaTerm {
                    var_name,
                    var_strict,
                    body: Box::new(new_body),
                });
                (new_lambda, has_changed)
            },
            _ => (self, false),
        }
    }

    fn get_all_lambda_vars(&self, lambda_vars_in_use: &mut HashSet<String>) {
        match &self.expr {
            Expr::LambdaTerm {var_name: name, body: lambda_body, ..} => {
                lambda_vars_in_use.insert(name.clone());
                lambda_body.get_all_lambda_vars(lambda_vars_in_use);
            },
            Expr::Redex(left, right) => {
                left.get_all_lambda_vars(lambda_vars_in_use);
                right.get_all_lambda_vars(lambda_vars_in_use);
            },
            _ => {},
        }
    }

    fn alpha_convert(&mut self,
                     lambda_vars_left: &mut HashSet<String>,
                     lambda_vars_right: &HashSet<String>,
                     conversions: &mut HashMap<String, String>) {
        match &mut self.expr {
            Expr::LambdaTerm {var_name: name, body: lambda_body, .. } => {
                if let Some(new_name) = get_next_avail_name(name, lambda_vars_left, lambda_vars_right) {
                    lambda_vars_left.insert(new_name.clone());
                    conversions.insert(name.clone(), new_name.clone());
                    *name = new_name;
                }
                lambda_body.alpha_convert(lambda_vars_left, lambda_vars_right, conversions);
            },
            Expr::Redex(left, right) => {
                left.alpha_convert(lambda_vars_left, lambda_vars_right, conversions);
                right.alpha_convert(lambda_vars_left, lambda_vars_right, conversions);
            }
            Expr::Var {name, is_free, } => {
                if !*is_free {
                    if let Some(new_name) = conversions.get(name) {
                        *name = new_name.clone();
                    }
                }
            },
        }
    }

    fn replace_bound_var(&mut self,
                         arg: &Ast,
                         var_name: &str,
                         lambda_vars: &mut HashSet<String>) {
        match &mut self.expr {
            Expr::Redex(left, right) => {
                left.replace_bound_var(arg, var_name, lambda_vars);
                right.replace_bound_var(arg, var_name, lambda_vars);
            },
            Expr::LambdaTerm { body: lambda_body, .. } => {
                lambda_body.replace_bound_var(arg, var_name, lambda_vars);
            },
            Expr::Var{ name, is_free } => {
                if !*is_free && var_name == name {
                    let mut arg_captured = arg.clone();
                    arg_captured.capture_free_vars(lambda_vars);
                    self.expr = arg_captured.expr;
                    self.reduced_last = true;
                }
            },
        };
    }

    fn capture_free_vars(&mut self, lambda_vars: &HashSet<String>) {
        match &mut self.expr {
            Expr::Var{ name, is_free } => {
                if *is_free && lambda_vars.contains(name) {
                    *is_free = false;
                }
            },
            Expr::LambdaTerm { body: lambda_body, .. } => {
                lambda_body.capture_free_vars(lambda_vars);
            },
            Expr::Redex(right, left) => {
                right.capture_free_vars(lambda_vars);
                left.capture_free_vars(lambda_vars);
            },
        }
    }

    // use when the redex's argument has been reduced because of a strict
    // variable and the original redex must be reconstructed, e.g.
    //  (\!x -> x) ((\x -> x) a)
    // becoming
    //  (\!x -> x) a
    fn strict_var_reconstruct_redex(var_name: String,
                                    var_strict: bool,
                                    lambda_body: Box<Ast>,
                                    right: Box<Ast>) -> Ast {
        let lambda_term = Ast::new(Expr::LambdaTerm{
            var_name,
            var_strict,
            body: lambda_body,
        });
        Ast::new(Expr::Redex(Box::new(lambda_term), right))
    }

    fn actual_fmt(&self, f: &mut Formatter,
                  outer_term_is_lambda: bool) -> fmt::Result {
        let use_color = self.reduced_last && !f.alternate();
        if use_color {
            write!(f, "\x1B[32m")?; // green
        }

        match &self.expr {
            Expr::Redex(left, right) => {
                let mut right_paren_needed = false;
                if let Expr::Redex(_,_) = right.expr {
                    right_paren_needed = true;
                }

                left.actual_fmt(f, false)?;
                write!(f, " ")?;

                if right_paren_needed {
                    write!(f, "(")?;
                }
                right.actual_fmt(f, false)?;
                if right_paren_needed {
                    write!(f, ")")?;
                }
            },
            Expr::LambdaTerm { var_name: name, var_strict, body: lambda_body } => {
                let paren_needed = !outer_term_is_lambda;
                if paren_needed {
                    write!(f, "(")?;
                }
                if outer_term_is_lambda {
                    write!(f, " ")?;
                } else {
                    if f.alternate() {
                        write!(f, "\\")?;
                    } else {
                        write!(f, "??")?;
                    }
                }
                if *var_strict {
                        write!(f, "!")?;
                }
                write!(f, "{}", name)?;
                match lambda_body.expr {
                    Expr::LambdaTerm { .. } => {},
                    _ => write!(f, ". ")?,
                }
                lambda_body.actual_fmt(f, true)?;

                if paren_needed {
                    write!(f, ")")?;
                }
            },
            Expr::Var { name, is_free: _ } => write!(f, "{}", name)?,
        }

        if use_color {
            write!(f, "\x1B[0m")?; // undo color selection
        }
        Ok(())
    }
}

/// If a program will read the output, use the alternate formatter,
/// which does not use ANSI color escapes or non-ASCII unicode characters.
///
impl Display for Ast {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.actual_fmt(f, false)
    }
}

fn get_next_avail_name(name: &str,
                       names_left: &HashSet<String>,
                       names_right: &HashSet<String>) -> Option<String> {
    if !names_left.contains(name) {
        return None;
    }
    let (prefix, mut num): (&str, i32) = match name.chars().position(|x: char| x.is_numeric()) {
        None => (&name, 0),
        Some(i) => (&name[..i], name[i..].parse::<i32>()
                    .expect(&format!("failed to convert variable suffix to number: '{}'", &name[i..])))
    };
    let mut new_name;
    loop {
        num += 1; // start from 1: the var without number suffix was the "0th"
        new_name = format!("{}{}", prefix, num.to_string());
        if !names_left.contains(&new_name) && !names_right.contains(&new_name) {
            return Some(new_name);
        }
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

    fn last(mut ast: Box<Ast>) -> Box<Ast> {
        ast.reduced_last = true;
        ast
    }

    fn last_no_box(mut ast: Ast) -> Ast {
        ast.reduced_last = true;
        ast
    }

    fn zero_reductions_test(ast: Ast) {
        let expected = ast.clone();
        let parser = Parser::new();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(!has_changed);
        assert_eq!(expected, ast);
    }

    fn one_reduction_test(ast: Ast, expected: Ast, expected_final: Ast) {
        let parser = Parser::new();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected, ast);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(!has_changed);
        assert_eq!(expected_final, ast);
    }

    fn two_reduction_test(ast: Ast, expected1: Ast, expected2: Ast, expected_final: Ast) {
        let parser = Parser::new();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected1, ast);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected2, ast);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(!has_changed);
        assert_eq!(expected_final, ast);
    }

    #[test]
    fn not_redex1() {
        let ast = free_var_no_box("a");
        zero_reductions_test(ast);
    }

    #[test]
    fn not_redex2() {
        let ast = lambda_no_box("x", false, bound_var("x"));
        zero_reductions_test(ast);
    }

    #[test]
    fn not_redex3() {
        let ast = lambda_no_box(
            "x", false,
            lambda("y", false, redex(bound_var("x"), bound_var("x")))
        );
        zero_reductions_test(ast);
    }

    #[test]
    fn fake_redex1() {
        let ast = redex_no_box(free_var("a"), free_var("b"));
        zero_reductions_test(ast);
    }

    #[test]
    fn fake_redex2() {
        let ast = redex_no_box(
            redex(free_var("a"), free_var("b")),
            free_var("c")
        );
        zero_reductions_test(ast);
    }

    #[test]
    fn fake_redex3() {
        let ast = redex_no_box(
            free_var("a"),
            redex(free_var("b"), free_var("c")),
        );
        zero_reductions_test(ast);
    }

    #[test]
    fn single_bound_var() {
        let ast = redex_no_box(
            lambda("x", false, bound_var("x")),
            free_var("a")
        );
        let expected = last_no_box(free_var_no_box("a"));
        let expected_final = free_var_no_box("a");
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn multiple_bound_vars() {
        let ast = redex_no_box(
            lambda("x", false, redex(
                    redex(bound_var("x"), bound_var("x")),
                    bound_var("x")
            )), free_var("a")
        );
        let expected = redex_no_box(
            redex(last(free_var("a")), last(free_var("a"))),
            last(free_var("a"))
        );
        let expected_final = redex_no_box(
            redex(free_var("a"), free_var("a")),
            free_var("a")
        );
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn one_bound_some_free_vars() {
        let ast = redex_no_box(
            lambda("x", false, redex(
                    redex(free_var("a"), bound_var("x")),
                    free_var("b")
            )), free_var("c")
        );
        let expected = redex_no_box(
            redex(free_var("a"), last(free_var("c"))),
            free_var("b")
        );
        let expected_final = redex_no_box(
            redex(free_var("a"), free_var("c")),
            free_var("b")
        );
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn two_lambdas_redex() {
        let ast = redex_no_box(
            lambda("x", false, bound_var("x")),
            lambda("y", false, bound_var("y")),
        );
        let expected = last_no_box(lambda_no_box("y", false, bound_var("y")));
        let expected_final = lambda_no_box("y", false, bound_var("y"));
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn constant_lambda() {
        let ast = redex_no_box(
            lambda("x", false, free_var("a")),
            free_var("b"),
        );
        let expected = free_var_no_box("a");
        let expected_final = expected.clone();
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn nested_lambdas() {
        let ast = redex_no_box(
            lambda("x", false,
                   lambda("y", false, redex(bound_var("x"), bound_var("y")))),
            free_var("a"),
        );
        let expected = lambda_no_box("y", false,
                                     redex(last(free_var("a")), bound_var("y")));
        let expected_final = lambda_no_box("y", false,
                                           redex(free_var("a"), bound_var("y")));
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn nested_lambdas_multilevel_subst() {
        // (lambda x . x a (lambda y . x y a (lambda z . x y z a))) b
        let ast = redex_no_box(
            lambda("x", false, redex(
                    redex(bound_var("x"), free_var("a")),
                    lambda("y", false, redex(
                            redex(
                                redex(bound_var("x"), bound_var("y")),
                                free_var("a")
                            ),
                            lambda("z", false, redex(
                                       redex(
                                           redex(bound_var("x"), bound_var("y")),
                                           bound_var("z")
                                        ),
                                        free_var("a"),
                            ))
                    ))
            )),
            free_var("b"),
        );
        let expected = redex_no_box(
            redex(last(free_var("b")), free_var("a")),
            lambda("y", false, redex(
                    redex(redex(last(free_var("b")), bound_var("y")), free_var("a")),
                    lambda("z", false, redex(
                               redex(
                                   redex(last(free_var("b")), bound_var("y")),
                                   bound_var("z"),
                               ),
                               free_var("a"),
                    )),
            )),
        );
        let expected_final = redex_no_box(
            redex(free_var("b"), free_var("a")),
            lambda("y", false, redex(
                    redex(redex(free_var("b"), bound_var("y")), free_var("a")),
                    lambda("z", false, redex(
                               redex(
                                   redex(free_var("b"), bound_var("y")),
                                   bound_var("z"),
                               ),
                               free_var("a"),
                    )),
            )),
        );
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn reduces_to_itself() {
        let ast = redex_no_box(
            lambda("x", false, redex(bound_var("x"), bound_var("x"))),
            lambda("x", false, redex(bound_var("x"), bound_var("x"))),
        );
        let expected = redex_no_box(
            last(lambda("x", false, redex(bound_var("x"), bound_var("x")))),
            last(lambda("x", false, redex(bound_var("x"), bound_var("x")))),
        );
        let parser = Parser::new();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected, ast);
    }

    #[test]
    fn two_stage_normal_order() {
        let ast = redex_no_box(
            lambda("x", false, bound_var("x")),
            redex(lambda("y", false, bound_var("y")), free_var("a"))
        );
        let expected1 = last_no_box(redex_no_box(
            lambda("y", false, bound_var("y")),
            free_var("a")
        ));
        let expected2 = last_no_box(free_var_no_box("a"));
        let expected_final = free_var_no_box("a");

        two_reduction_test(ast, expected1, expected2, expected_final);
    }

    #[test]
    fn two_stage_produced_redex() {
        let ast = redex_no_box(
            lambda("x", false, redex(bound_var("x"), bound_var("x"))),
            lambda("y", false, bound_var("y")),
        );
        let expected1 = redex_no_box(
            last(lambda("y", false, bound_var("y"))),
            last(lambda("y", false, bound_var("y"))),
        );
        let expected2 = last_no_box(lambda_no_box("y", false, bound_var("y")));
        let expected_final = lambda_no_box("y", false, bound_var("y"));

        two_reduction_test(ast, expected1, expected2, expected_final);
    }

    #[test]
    fn mandatory_normal_order() {
        let ast = redex_no_box(
            lambda("x", false, free_var("a")),
            redex(
                lambda("x", false, redex(bound_var("x"), bound_var("x"))),
                lambda("x", false, redex(bound_var("x"), bound_var("x"))),
            ),
        );
        let expected = free_var_no_box("a");
        let expected_final = expected.clone();

        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn reduction_inside_lambda_body() {
        let ast = lambda_no_box(
            "x", false,
            redex(lambda("a", false, bound_var("a")), bound_var("x"))
        );
        let expected = lambda_no_box("x", false, last(bound_var("x")));
        let expected_final = lambda_no_box("x", false, bound_var("x"));

        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn capture_free_var1() {
        let ast = redex_no_box(
            lambda("x", false, lambda("y", false, bound_var("x"))),
            free_var("y")
        );
        let expected = lambda_no_box("y", false, last(bound_var("y")));
        let expected_final = lambda_no_box("y", false, bound_var("y"));

        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn capture_free_var2() {
        let ast = redex_no_box(
            lambda("x", false, lambda("y", false, bound_var("x"))),
            lambda("z", false, free_var("y"))
        );
        let expected = lambda_no_box("y", false,
                                     last(lambda("z", false, bound_var("y"))));
        let expected_final = lambda_no_box("y", false,
                                           lambda("z", false, bound_var("y")));

        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn capture_free_var3() {
        let ast = redex_no_box(
            lambda("x", false, lambda("y", false, bound_var("x"))),
            redex(free_var("a"), free_var("y")),
        );

        let expected = lambda_no_box("y", false,
                                     last(redex(free_var("a"), bound_var("y"))));
        let expected_final = lambda_no_box("y", false,
                                           redex(free_var("a"), bound_var("y")));

        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn dont_recapture_bound_var() {
        let ast = lambda_no_box(
            "x", false,
            redex(
                lambda("a", false, lambda("b", false, bound_var("a"))),
                bound_var("x"),
            ),
        );
        let expected = lambda_no_box("x", false,
                                     lambda("b", false, last(bound_var("x"))));
        let expected_final = lambda_no_box("x", false,
                                           lambda("b", false, bound_var("x")));

        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn alpha_conversion1() {
        let ast = redex_no_box(
            lambda("x", false, lambda("y", false, bound_var("x"))),
            lambda("y", false, bound_var("y"))
        );
        // should reduce to \y y1 -> y1 but may reduce to \y y -> y if alpha
        // conversion is not being done properly

        let expected = lambda_no_box(
            "y", false,
            last(lambda("y1", false, bound_var("y1"))),
        );
        let expected_final = lambda_no_box(
            "y", false,
            lambda("y1", false, bound_var("y1")),
        );
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn alpha_conversion2() {
        let ast = redex_no_box(
            lambda("x", false,
                   lambda("y", false, lambda("y1", false, bound_var("x")))),
            lambda("y", false, bound_var("y")),
        );
        let expected = lambda_no_box(
            "y", false,
            lambda("y1", false, last(lambda("y2", false, bound_var("y2"))))
        );
        let expected_final = lambda_no_box(
            "y", false,
            lambda("y1", false, lambda("y2", false, bound_var("y2")))
        );
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn several_stages1() {
        let expr = redex_no_box(
            redex(
                redex(
                    lambda("x", false,
                           lambda("y", false,
                                  lambda("z", false,
                                         redex(
                                             redex(bound_var("x"), bound_var("z")),
                                             redex(bound_var("y"), bound_var("z")),
                                         ),
                     ))),
                     lambda("a", false, lambda("b", false, bound_var("a"))),
                ),
                lambda("c", false, lambda("d", false, bound_var("d"))),
            ),
            free_var("n")
        ); // S K K n

        let expected1 = redex_no_box(
            redex(
                lambda("y", false,
                       lambda("z", false,
                              redex(
                                  redex(
                                      last(lambda("a", false,
                                                  lambda("b", false,
                                                         bound_var("a")))),
                                      bound_var("z"),
                                  ),
                                  redex(bound_var("y"), bound_var("z")),
                              )
                       )
                ),
                lambda("c", false, lambda("d", false, bound_var("d"))),
            ),
            free_var("n")
        );

        let expected2 = redex_no_box(
            lambda("z", false,
                   redex(
                       redex(
                           lambda("a", false, lambda("b", false, bound_var("a"))),
                           bound_var("z"),
                       ),
                       redex(
                           last(lambda("c", false, lambda("d", false, bound_var("d")))),
                           bound_var("z"),
                       ),
                   ),
            ),
            free_var("n")
        );

        let expected3 = redex_no_box(
            redex(
                lambda("a", false, lambda("b", false, bound_var("a"))),
                last(free_var("n")),
            ),
            redex(
                lambda("c", false, lambda("d", false, bound_var("d"))),
                last(free_var("n")),
            ),
        );

        let expected4 = redex_no_box(
            lambda("b", false, last(free_var("n"))),
            redex(
                lambda("c", false, lambda("d", false, bound_var("d"))),
                free_var("n"),
            ),
        );
        let expected_final = free_var_no_box("n");
        
        let parser = Parser::new();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected1, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected2, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected3, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected4, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected_final, expr);
    }

    #[test]
    fn several_stages_alpha_conversion() {
        let expr = redex_no_box(
            redex(
                lambda("x", false,
                       lambda("y", false,
                              lambda("z", false,
                                     redex(
                                         bound_var("x"),
                                         redex(bound_var("y"), bound_var("z")),
                                     ),
                ))),
                lambda("z", false, bound_var("z")),
            ),
            lambda("z", false, bound_var("z")),
        );

        let expected1 = redex_no_box(
            lambda("y", false,
                   lambda("z", false,
                          redex(
                              last(lambda("z1", false, bound_var("z1"))),
                              redex(bound_var("y"), bound_var("z")),
                          ),
            )),
            lambda("z", false, bound_var("z"))
        );

        let expected2 = lambda_no_box(
            "z", false,
            redex(
                lambda("z1", false, bound_var("z1")),
                redex(
                    last(lambda("z2", false, bound_var("z2"))),
                    bound_var("z")
                ),
            ),
        );

        let parser = Parser::new();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected1, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected2, expr);
    }

    #[test]
    fn several_stages2() {
        let expr = redex_no_box(
            redex(
                lambda("x", false,
                       lambda("y", false,
                              lambda("z", false,
                                     redex(
                                         redex(bound_var("x"), bound_var("z")),
                                         redex(bound_var("y"), bound_var("z")),
                                     ),
                ))),
                lambda("a", false, lambda("b", false, bound_var("a"))),
            ),
            lambda("c", false, lambda("d", false, bound_var("d"))),
        );

        let expected1 = redex_no_box(
            lambda("y", false,
                   lambda("z", false,
                          redex(
                              redex(
                                  last(lambda("a", false, lambda("b", false, bound_var("a")))),
                                  bound_var("z"),
                              ),
                              redex(bound_var("y"), bound_var("z")),
                          ),
            )),
            lambda("c", false, lambda("d", false, bound_var("d"))),
        );

        let expected2 = lambda_no_box(
            "z", false,
            redex(
                redex(
                    lambda("a", false, lambda("b", false, bound_var("a"))),
                    bound_var("z"),
                ),
                redex(
                    last(lambda("c", false, lambda("d", false, bound_var("d")))),
                    bound_var("z"),
                ),
            ),
        );

        let expected3 = lambda_no_box(
            "z", false,
            redex(
                lambda("b", false, last(bound_var("z"))),
                redex(
                    lambda("c", false, lambda("d", false, bound_var("d"))),
                    bound_var("z"),
                ),
            ),
        );

        let expected4 = lambda_no_box("z", false, bound_var("z"));

        let parser = Parser::new();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected1, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected2, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected3, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected4, expr);
    }

    #[test]
    fn strict_var_usual_reduction() {
        let ast = redex_no_box(
            lambda("x", true, bound_var("x")),
            free_var("a"),
        );
        let expected1 = last_no_box(free_var_no_box("a"));
        let expected_final = free_var_no_box("a");

        let parser = Parser::new();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected1, ast);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(!has_changed);
        assert_eq!(expected_final, ast);
    }

    #[test]
    fn strict_var_eval_unused_arg() {
        let ast = redex_no_box(
            lambda("x", true, free_var("a")),
            redex(
                lambda("y", false, bound_var("y")),
                free_var("b"),
            ),
        );
        let expected1 = redex_no_box(
            lambda("x", true, free_var("a")),
            last(free_var("b")),
        );
        let expected2 = free_var_no_box("a");
        let expected_final = free_var_no_box("a");
        two_reduction_test(ast, expected1, expected2, expected_final);
    }

    #[test]
    fn strict_val_infinite_loop() {
        let ast = redex_no_box(
            lambda("x", true, free_var("a")),
            redex(
                lambda("y", false, redex(bound_var("y"), bound_var("y"))),
                lambda("y", false, redex(bound_var("y"), bound_var("y"))),
            ),
        );
        let expected = redex_no_box(
            lambda("x", true, free_var("a")),
            redex(
                last(lambda("y", false, redex(bound_var("y"), bound_var("y")))),
                last(lambda("y", false, redex(bound_var("y"), bound_var("y")))),
            ),
        );
        let parser = Parser::new();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(expected, ast);
    }

    #[test]
    fn def_replaced_in_free_lambda_var() {
        let mut parser = Parser::new();
        parser.insert_symbol("I", lambda_no_box("x", false, bound_var("x")));

        let ast = lambda_no_box(
            "y", false,
            redex(
                free_var("I"),
                bound_var("y")
            ),
        );
        let expected1 = lambda_no_box(
            "y", false,
            redex(
                last(lambda("x", false,
                       bound_var("x"),
                )),
                bound_var("y"),
            ),
        );
        let expected2 = lambda_no_box(
            "y", false,
            last(bound_var("y")),
        );
        let expected_final = lambda_no_box(
            "y", false,
            bound_var("y"),
        );
        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(ast, expected1);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(ast, expected2);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(!has_changed);
        assert_eq!(ast, expected_final);
    }

    #[test]
    fn def_not_replaced_in_bound_var() {
        let mut parser = Parser::new();
        parser.insert_symbol("a", lambda_no_box("x", false, bound_var("x")));

        let ast = lambda_no_box(
            "a", false,
            redex(bound_var("a"), bound_var("a")),
        );
        let expected = ast.clone();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(!has_changed);
        assert_eq!(ast, expected);
    }

    #[test]
    fn replace_last_step() {
        let mut parser = Parser::new();
        parser.insert_symbol("I", lambda_no_box("x", false, bound_var("x")));

        let ast = free_var_no_box("I");
        let expected1 = last_no_box(lambda_no_box("x", false, bound_var("x")));
        let expected2 = lambda_no_box("x", false, bound_var("x"));

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(!has_changed);

        let (ast, has_changed) = ast.last_step_beta_reduce(&parser);
        assert!(has_changed);
        assert_eq!(ast, expected1);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(!has_changed);
        assert_eq!(ast, expected2);
    }

    #[test]
    fn def_with_redex() {
       let mut parser = Parser::new();
        parser.insert_symbol(
            "a",
            redex_no_box(
                lambda("x", false, bound_var("x")),
                lambda("y", false, bound_var("y"))
            ),
        );
        let ast = redex_no_box(free_var("a"), free_var("b"));
        let expected1 = redex_no_box(
            last(redex(
                lambda("x", false, bound_var("x")),
                lambda("y", false, bound_var("y")),
            )),
            free_var("b"),
        );
        let expected2 = redex_no_box(
            last(lambda("y", false, bound_var("y"))),
            free_var("b"),
        );
        let expected3 = last_no_box(free_var_no_box("b"));
        let expected_final = free_var_no_box("b");

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(ast, expected1);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(ast, expected2);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(ast, expected3);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(!has_changed);
        assert_eq!(ast, expected_final);
    }

    #[test]
    fn alpha_conversion_def() {
        let mut parser = Parser::new();
        parser.insert_symbol("id", lambda_no_box("x", false, bound_var("x")));

        let ast = lambda_no_box(
            "x", false,
            redex(
                free_var("id"),
                bound_var("x"),
            ),
        );
        let expected1 = lambda_no_box(
            "x", false,
            redex(
                last(lambda("x1", false, bound_var("x1"))),
                bound_var("x"),
            ),
        );
        let expected2 = lambda_no_box(
            "x", false,
            last(bound_var("x")),
        );
        let expected_final = lambda_no_box(
            "x", false,
            bound_var("x"),
        );

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert_eq!(ast, expected1);
        assert!(has_changed);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert_eq!(ast, expected2);
        assert!(has_changed);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert_eq!(ast, expected_final);
        assert!(!has_changed);
    }

    #[test]
    fn simultaneous_alpha_conversions1() {
        let ast = redex_no_box(
            lambda("f", false,
                   redex(
                       lambda("g", false,
                              lambda("h", false,
                                     redex(bound_var("h"), bound_var("g")),
                       )),
                       lambda("h", false,
                              redex(bound_var("h"), bound_var("f")),
                       ),
                   ),
            ),
            lambda("h", false, bound_var("h")),
        ); // (\f -> (\g h -> h g) (\h -> h f)) (\h -> h)

        let expected1 = redex_no_box(
           lambda("g", false,
                  lambda("h", false,
                         redex(bound_var("h"), bound_var("g")),
           )),
           lambda("h", false,
                  redex(
                      bound_var("h"),
                      last(lambda("h1", false, bound_var("h1"))),
                  )
            ),
        ); // (\g h. h g) (\h. h (\h1. h1))

        let expected2 = lambda_no_box(
            "h", false,
            redex(
                bound_var("h"),
                last(lambda("h2", false,
                       redex(
                           bound_var("h2"),
                           lambda("h1", false, bound_var("h1")),
                       )
                 )),
            ),
        );

        let parser = Parser::new();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert_eq!(ast, expected1);
        assert!(has_changed);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert_eq!(ast, expected2);
        assert!(has_changed);
    }

    #[test]
    fn simultaneous_alpha_conversions2() {
        let ast = redex_no_box(
            lambda("f", false,
                redex(
                    lambda("g", false,
                           lambda("h", false,
                                  redex(
                                      bound_var("h"),
                                      redex(bound_var("g"), bound_var("f")),
                                  )
                    )),
                    lambda("h", false,
                           redex(bound_var("h"), bound_var("f")),
                    ),
                ),
            ),
            lambda("h", false, bound_var("h")),
        ); // (\f. (\g h. h (g f)) (\h. h f)) (\h. h)
        let expected1 = redex_no_box(
            lambda("g", false,
                   lambda("h", false,
                          redex(
                              bound_var("h"),
                              redex(
                                  bound_var("g"),
                                  last(lambda("h1", false, bound_var("h1")))
                          )),
            )),
            lambda("h", false,
                   redex(
                       bound_var("h"),
                       last(lambda("h1", false, bound_var("h1"))),
                   ),
            ),
        ); // (\g h. h (g (\h1. h1))) (\h. h (\h1. h1))
        let expected2 = lambda_no_box(
            "h", false,
            redex(
                bound_var("h"),
                redex(
                    last(lambda("h2", false,
                                redex(
                                    bound_var("h2"),
                                    lambda("h3", false, bound_var("h3")),
                                ),
                    )),
                    lambda("h1", false, bound_var("h1")),
                ),
            )
        ); // (\h. h ((\h2. h2 (\h3. h3)) (\h1. h1)))

        // reduction could go on, but we're only interested in these steps

        let parser = Parser::new();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert_eq!(ast, expected1);
        assert!(has_changed);

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert_eq!(ast, expected2);
        assert!(has_changed);
    }

    /*
     * commented out since unnecessary alpha conversions do not lead to
     * wrong reductions and it'd be too complicated to eliminate them.
    #[test]
    fn no_unnecessary_alpha_conversion() {
        let ast = redex_no_box(
            lambda("a",
                   redex(
                       bound_var("a"),
                       lambda("b", bound_var("b")),
                   ),
            ),
            lambda("b", bound_var("b")),
        ); // (\a -> a (\b -> b)) (\b -> b)

        let expected1 = redex_no_box(
            // might become b1 if unnecessary alpha conversion takes place
            lambda("b", bound_var("b")),
            lambda("b", bound_var("b")),
        );

        let parser = Parser::new();

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(ast, expected1);
    }
    */

    #[test]
    fn eager_eval_symbol_subst() {
        let mut parser = Parser::new();
        parser.insert_symbol("I", lambda_no_box("x", false, bound_var("x")));

        let ast = redex_no_box(
            lambda("y", true, bound_var("y")),
            free_var("I"),
        );
        let expected1 = redex_no_box(
            lambda("y", true, bound_var("y")),
            last(lambda("x", false, bound_var("x")))
        );

        let (ast, has_changed) = ast.beta_reduce_once(&mut HashSet::new(), &parser);
        assert!(has_changed);
        assert_eq!(ast, expected1);
    }

    #[test]
    fn alpha_conversion_numeric_vars1() {
        let ast = redex_no_box(
            lambda("x", false,
                   lambda("x1", false,
                          redex(bound_var("x1"), bound_var("x")))),
            lambda("x1", false,
                   bound_var("x1")),
        );
        let expected = lambda_no_box(
            "x1", false,
            redex(
                bound_var("x1"),
                last(lambda("x2", false, bound_var("x2"))),
            ));
        let expected_final = lambda_no_box(
            "x1", false,
            redex(
                bound_var("x1"),
                lambda("x2", false, bound_var("x2")),
            ));
        one_reduction_test(ast, expected, expected_final);
    }

    #[test]
    fn alpha_conversion_numeric_vars2() {
        let ast = redex_no_box(
            lambda("x", false,
                   lambda("x1", false,
                          redex(bound_var("x1"), bound_var("x")))),
            redex(
                lambda("x1", false, bound_var("x1")),
                lambda("x1", false, bound_var("x1")),
            ),
        );
        let expected1 = lambda_no_box(
            "x1", false,
            redex(
                bound_var("x1"),
                last(redex(
                    lambda("x2", false, bound_var("x2")),
                    lambda("x3", false, bound_var("x3")),
                )),
            ));
        let expected2 = lambda_no_box(
            "x1", false,
            redex(
                bound_var("x1"),
                last(lambda("x3", false, bound_var("x3"))),
            ));
        let expected_final = lambda_no_box(
            "x1", false,
            redex(
                bound_var("x1"),
                lambda("x3", false, bound_var("x3")),
            ));
        two_reduction_test(ast, expected1, expected2, expected_final);
    }

    #[test]
    fn alpha_conversion_numeric_vars3() {
        let ast = redex_no_box(
            lambda("a", false,
                   lambda("x4", false,
                          lambda("x2", false,
                                 lambda("x1", false,
                                        lambda("x", false,
                                               bound_var("a")))))),
            lambda("x", false, bound_var("x")),
        );
        let expected1 = lambda_no_box(
            "x4", false,
            lambda("x2", false,
                   lambda("x1", false,
                          lambda("x", false,
                                 last(lambda("x3", false, bound_var("x3")))))),
        );
        let expected_final = lambda_no_box(
            "x4", false,
            lambda("x2", false,
                   lambda("x1", false,
                          lambda("x", false,
                                 lambda("x3", false, bound_var("x3"))))),
        );
        one_reduction_test(ast, expected1, expected_final);
    }

    #[test]
    fn multiple_alpha_conversions_numeric_vars() {
        let ast = redex_no_box(
            lambda("y", false,
                lambda("f", false,
                    redex(
                        redex(
                            bound_var("f"),
                            bound_var("y"),
                        ),
                        lambda("x", false, bound_var("x")),
                    ),
                ),
            ),
            lambda(
                "x1", false,
                lambda(
                    "x", false,
                    redex(
                        bound_var("x1"),
                        bound_var("x")
                    ),
                ),
            ),
        );
        let expected1 = lambda_no_box(
            "f", false,
            redex(
                redex(
                    bound_var("f"),
                    last(lambda(
                        "x1", false,
                        lambda(
                            "x2", false,
                            redex(
                                bound_var("x1"),
                                bound_var("x2")
                            ),
                        ),
                    )),
                ),
                lambda("x", false, bound_var("x")),
            ),
        );
        let expected_final = lambda_no_box(
            "f", false,
            redex(
                redex(
                    bound_var("f"),
                    lambda(
                        "x2", false,
                        lambda(
                            "x1", false,
                            redex(
                                bound_var("x1"),
                                bound_var("x2")
                            ),
                        ),
                    ),
                ),
                lambda("x", false, bound_var("x")),
            ),
        );
        one_reduction_test(ast, expected1, expected_final);
    }
}
