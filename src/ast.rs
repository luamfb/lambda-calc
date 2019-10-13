use std::fmt;
use std::fmt::{Display, Formatter};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Ast {
    expr: Expr,
    reduced_last: bool,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expr {
    Var { name: String, is_free: bool, },
    LambdaTerm {var_name: String, body: Box<Ast>},
    Redex(Box<Ast>, Box<Ast>),
}

impl Ast {
    pub fn new(expr: Expr) -> Ast {
        Ast {
            expr,
            reduced_last: false,
        }
    }

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
    /// let parser = Parser::new();
    /// let redex = parser.parse("(lambda x . a) ((lambda y . y y) (lambda y . y y))");
    /// let non_redex = redex.beta_reduce_print();
    /// assert_eq!(non_redex, Expr::Var{name: "a".to_string(), is_free: true});
    /// ```
    ///
    /// This function does not attempt to predict infinite loops.
    pub fn beta_reduce_print(self) -> Ast {
        self.beta_reduce(true)
    }

    /// Identical to beta_reduce_print() but doesn't print anything.
    pub fn beta_reduce_quiet(self) -> Ast {
        self.beta_reduce(false)
    }

    fn beta_reduce(mut self, should_print: bool) -> Ast {
        loop {
            let pair = self.beta_reduce_once(&mut HashSet::new());
            self = pair.0;
            let expr_has_changed = pair.1;
            if !expr_has_changed {
                return self;
            }
            if should_print {
                println!("= {}", self);
            }
        }
    }

    fn beta_reduce_once(mut self, lambda_vars_in_use: &mut HashSet<String>) -> (Ast, bool) {
        self.unset_reduced_last();
        self.beta_reduce_once_recur(lambda_vars_in_use)
    }

    fn unset_reduced_last(&mut self) {
        self.reduced_last = false;
        match &mut self.expr {
            Expr::Redex(left, right) => {
                left.unset_reduced_last();
                right.unset_reduced_last();
            },
            Expr::LambdaTerm { var_name: _, body, } => {
                body.unset_reduced_last();
            },
            _ => {},
        }
    }

    // Returns the expression after attemtping to apply a single beta-reduction,
    // and a boolean which is whether or not a reduction could be made.
    // Call unset_reduced_last() before this.
    //
    fn beta_reduce_once_recur(self, lambda_vars_in_use: &mut HashSet<String>) -> (Ast, bool) {
        match self.expr {
            Expr::Redex(left, mut right) => {
                if let Expr::LambdaTerm {var_name, body: mut lambda_body} = left.expr {
                    // note that we don't include this lambda's var name in
                    // lambda_vars_in_use, since it's the variable that will
                    // be replaced by reduction
                    //
                    lambda_body.get_all_lambda_vars(lambda_vars_in_use);
                    {
                        let mut conversions = HashMap::new();
                        right.alpha_convert(lambda_vars_in_use, &mut conversions);
                    }
                    lambda_body.replace_bound_var(&right, &var_name, lambda_vars_in_use);

                    lambda_vars_in_use.clear();

                    let new_ast = *lambda_body;
                    (new_ast, true)
                } else {
                    let (new_left, has_changed)
                        = left.beta_reduce_once_recur(lambda_vars_in_use);
                    if has_changed {
                        let new_ast = Ast::new(Expr::Redex(Box::new(new_left), right));
                        return (new_ast, true);
                    }
                    let (new_right, has_changed)
                        = right.beta_reduce_once_recur(lambda_vars_in_use);
                    let new_ast = Ast::new(Expr::Redex(
                        Box::new(new_left),
                        Box::new(new_right)
                    ));
                    (new_ast, has_changed)
                }
            },
            Expr::LambdaTerm {var_name: name, body: lambda_body} => {
                //lambda_vars_in_use.insert(name.clone());

                let (new_body, has_changed)
                    = lambda_body.beta_reduce_once_recur(lambda_vars_in_use);

                //lambda_vars_in_use.remove(&name);

                let new_lambda = Ast::new(Expr::LambdaTerm {
                    var_name: name,
                    body: Box::new(new_body),
                });
                (new_lambda, has_changed)
            },
            _ => (self, false),
        }
    }

    fn get_all_lambda_vars(&self, lambda_vars_in_use: &mut HashSet<String>) {
        match &self.expr {
            Expr::LambdaTerm {var_name: name, body: lambda_body} => {
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

    fn alpha_convert(&mut self, lambda_vars_in_use: &mut HashSet<String>,
                     conversions: &mut HashMap<String, String>) {
        match &mut self.expr {
            Expr::LambdaTerm {var_name: name, body: lambda_body} => {
                if let Some(new_name) = get_next_avail_name(name, lambda_vars_in_use) {
                    lambda_vars_in_use.insert(name.clone());
                    conversions.insert(name.clone(), new_name.clone());
                    *name = new_name;
                }
                lambda_body.alpha_convert(lambda_vars_in_use, conversions);
            },
            Expr::Redex(left, right) => {
                left.alpha_convert(lambda_vars_in_use, conversions);
                right.alpha_convert(lambda_vars_in_use, conversions);
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
            Expr::LambdaTerm { var_name: _, body: lambda_body } => {
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
            Expr::LambdaTerm { var_name: _, body: lambda_body } => {
                lambda_body.capture_free_vars(lambda_vars);
            },
            Expr::Redex(right, left) => {
                right.capture_free_vars(lambda_vars);
                left.capture_free_vars(lambda_vars);
            },
        }
    }

    pub fn substitute_symbols_from(&mut self, symbol_table: &HashMap<String, Ast>) {
        match &mut self.expr {
            Expr::Redex(left, right) => {
                left.substitute_symbols_from(symbol_table);
                right.substitute_symbols_from(symbol_table);
            },
            Expr::LambdaTerm { var_name: _, body: lambda_body } => {
                lambda_body.substitute_symbols_from(symbol_table);
            },
            Expr::Var {name, is_free} => if *is_free {
                match symbol_table.get(name) {
                    None => return,
                    Some(ast) => self.expr = ast.clone().expr,
                };
            },
        }
    }

    fn actual_fmt(&self, f: &mut Formatter,
                  outer_term_is_lambda: bool) -> fmt::Result {
        if self.reduced_last {
            // ideally we should check if output is actually a tty
            // (and not e.g. a pipe) before doing this
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
            Expr::LambdaTerm { var_name: name, body: lambda_body } => {
                let paren_needed = !outer_term_is_lambda;
                if paren_needed {
                    write!(f, "(")?;
                }
                if outer_term_is_lambda {
                    write!(f, " {}", name)?;
                } else {
                    write!(f, "λ{}", name)?;
                }
                match lambda_body.expr {
                    Expr::LambdaTerm {var_name: _, body: _} => {},
                    _ => write!(f, ". ")?,
                }
                lambda_body.actual_fmt(f, true)?;

                if paren_needed {
                    write!(f, ")")?;
                }
            },
            Expr::Var { name, is_free: _ } => write!(f, "{}", name)?,
        }

        if self.reduced_last {
            write!(f, "\x1B[0m")?; // undo color selection
        }
        Ok(())
    }
}

impl Display for Ast {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.actual_fmt(f, false)
    }
}

fn get_next_avail_name(name: &str, names_in_use: &HashSet<String>) -> Option<String> {
    if !names_in_use.contains(name) {
        return None;
    }
    let mut new_name = name.to_string();
    while names_in_use.contains(&new_name) {
        new_name.push('\'');
    }
    Some(new_name)
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
    fn not_redex1() {
        let expr = free_var_no_box("a");
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn not_redex2() {
        let expr = lambda_no_box("x", bound_var("x"));
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn not_redex3() {
        let expr = lambda_no_box(
            "x",
            lambda("y", redex(bound_var("x"), bound_var("x")))
        );
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn fake_redex1() {
        let expr = redex_no_box(free_var("a"), free_var("b"));
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn fake_redex2() {
        let expr = redex_no_box(
            redex(free_var("a"), free_var("b")),
            free_var("c")
        );
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn fake_redex3() {
        let expr = redex_no_box(
            free_var("a"),
            redex(free_var("b"), free_var("c")),
        );
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn single_bound_var() {
        let expr = redex_no_box(
            lambda("x", bound_var("x")),
            free_var("a")
        );
        let expected = free_var_no_box("a");

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);
        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn multiple_bound_vars() {
        let expr = redex_no_box(
            lambda("x", redex(
                    redex(bound_var("x"), bound_var("x")),
                    bound_var("x")
            )), free_var("a")
        );
        let expected = redex_no_box(
            redex(free_var("a"), free_var("a")),
            free_var("a")
        );

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn one_bound_some_free_vars() {
        let expr = redex_no_box(
            lambda("x", redex(
                    redex(free_var("a"), bound_var("x")),
                    free_var("b")
            )), free_var("c")
        );
        let expected = redex_no_box(
            redex(free_var("a"), free_var("c")),
            free_var("b")
        );

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn two_lambdas_redex() {
        let expr = redex_no_box(
            lambda("x", bound_var("x")),
            lambda("y", bound_var("y")),
        );
        let expected = lambda_no_box("y", bound_var("y"));

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);
        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn constant_lambda() {
        let expr = redex_no_box(
            lambda("x", free_var("a")),
            free_var("b"),
        );
        let expected = free_var_no_box("a");

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn nested_lambdas() {
        let expr = redex_no_box(
            lambda("x", lambda("y", redex(bound_var("x"), bound_var("y")))),
            free_var("a"),
        );
        let expected = lambda_no_box("y", redex(free_var("a"), bound_var("y")));

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);
        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn nested_lambdas_multilevel_subst() {
        // (lambda x . x a (lambda y . x y a (lambda z . x y z a))) b
        let expr = redex_no_box(
            lambda("x", redex(
                    redex(bound_var("x"), free_var("a")),
                    lambda("y", redex(
                            redex(
                                redex(bound_var("x"), bound_var("y")),
                                free_var("a")
                            ),
                            lambda("z", redex(
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
            redex(free_var("b"), free_var("a")),
            lambda("y", redex(
                    redex(redex(free_var("b"), bound_var("y")), free_var("a")),
                    lambda("z", redex(
                               redex(
                                   redex(free_var("b"), bound_var("y")),
                                   bound_var("z"),
                               ),
                               free_var("a"),
                    )),
            )),
        );
        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);
        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn reduces_to_itself() {
        let expr = redex_no_box(
            lambda("x", redex(bound_var("x"), bound_var("x"))),
            lambda("x", redex(bound_var("x"), bound_var("x"))),
        );
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn two_stage_normal_order() {
        let expr = redex_no_box(
            lambda("x", bound_var("x")),
            redex(lambda("y", bound_var("y")), free_var("a"))
        );
        let expected1 = redex_no_box(
            lambda("y", bound_var("y")),
            free_var("a")
        );
        let expected2 = free_var_no_box("a");

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected1, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected2, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected2, expr);
    }

    #[test]
    fn two_stage_produced_redex() {
        let expr = redex_no_box(
            lambda("x", redex(bound_var("x"), bound_var("x"))),
            lambda("y", bound_var("y")),
        );
        let expected1 = redex_no_box(
            lambda("y", bound_var("y")),
            lambda("y", bound_var("y")),
        );
        let expected2 = lambda_no_box("y", bound_var("y"));

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected1, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected2, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected2, expr);
    }

    #[test]
    fn mandatory_normal_order() {
        let expr = redex_no_box(
            lambda("x", free_var("a")),
            redex(
                lambda("x", redex(bound_var("x"), bound_var("x"))),
                lambda("x", redex(bound_var("x"), bound_var("x"))),
            ),
        );
        let expected = free_var_no_box("a");

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn reduction_inside_lambda_body() {
        let expr = lambda_no_box(
            "x",
            redex(lambda("a", bound_var("a")), bound_var("x"))
        );
        let expected = lambda_no_box("x", bound_var("x"));

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn capture_free_var1() {
        let expr = redex_no_box(
            lambda("x", lambda("y", bound_var("x"))),
            free_var("y")
        );
        let expected = lambda_no_box("y", bound_var("y"));

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn capture_free_var2() {
        let expr = redex_no_box(
            lambda("x", lambda("y", bound_var("x"))),
            lambda("z", free_var("y"))
        );
        let expected = lambda_no_box("y", lambda("z", bound_var("y")));

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn capture_free_var3() {
        let expr = redex_no_box(
            lambda("x", lambda("y", bound_var("x"))),
            redex(free_var("a"), free_var("y")),
        );

        let expected = lambda_no_box("y", redex(free_var("a"), bound_var("y")));

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn dont_recapture_bound_var() {
        let expr = lambda_no_box(
            "x",
            redex(
                lambda("a", lambda("b", bound_var("a"))),
                bound_var("x"),
            ),
        );
        let expected = lambda_no_box("x", lambda("b", bound_var("x")));

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn alpha_conversion() {
        let expr = redex_no_box(
            lambda("x", lambda("y", bound_var("x"))),
            lambda("y", bound_var("y"))
        );
        // should reduce to \y y' -> y' but may reduce to \y y -> y if alpha
        // conversion is not being done properly

        let expected = lambda_no_box(
            "y",
            lambda("y'", bound_var("y'")),
        );

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn alpha_conversion2() {
        let expr = redex_no_box(
            lambda("x", lambda("y", lambda("y'", bound_var("x")))),
            lambda("y", bound_var("y")),
        );
        let expected = lambda_no_box(
            "y",
            lambda("y'", lambda("y''", bound_var("y''")))
        );

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn several_stages() {
        let expr = redex_no_box(
            redex(
                redex(
                    lambda("x",
                           lambda("y",
                                  lambda("z",
                                         redex(
                                             redex(bound_var("x"), bound_var("z")),
                                             redex(bound_var("y"), bound_var("z")),
                                         ),
                     ))),
                     lambda("a", lambda("b", bound_var("a"))),
                ),
                lambda("c", lambda("d", bound_var("d"))),
            ),
            free_var("n")
        ); // S K K n

        let expected1 = redex_no_box(
            redex(
                lambda("y",
                       lambda("z",
                              redex(
                                  redex(
                                      lambda("a", lambda("b", bound_var("a"))),
                                      bound_var("z"),
                                  ),
                                  redex(bound_var("y"), bound_var("z")),
                              )
                       )
                ),
                lambda("c", lambda("d", bound_var("d"))),
            ),
            free_var("n")
        );

        let expected2 = redex_no_box(
            lambda("z",
                   redex(
                       redex(
                           lambda("a", lambda("b", bound_var("a"))),
                           bound_var("z"),
                       ),
                       redex(
                           lambda("c", lambda("d", bound_var("d"))),
                           bound_var("z"),
                       ),
                   ),
            ),
            free_var("n")
        );

        let expected3 = redex_no_box(
            redex(
                lambda("a", lambda("b", bound_var("a"))),
                free_var("n"),
            ),
            redex(
                lambda("c", lambda("d", bound_var("d"))),
                free_var("n"),
            ),
        );

        let expected4 = redex_no_box(
            lambda("b", free_var("n")),
            redex(
                lambda("c", lambda("d", bound_var("d"))),
                free_var("n"),
            ),
        );
        let expected5 = free_var_no_box("n");

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected1, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected2, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected3, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected4, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected5, expr);
    }

    #[test]
    fn several_stages_alpha_conversion() {
        let expr = redex_no_box(
            redex(
                lambda("x",
                       lambda("y",
                              lambda("z",
                                     redex(
                                         bound_var("x"),
                                         redex(bound_var("y"), bound_var("z")),
                                     ),
                ))),
                lambda("z", bound_var("z")),
            ),
            lambda("z", bound_var("z")),
        );

        let expected1 = redex_no_box(
            lambda("y",
                   lambda("z",
                          redex(
                              lambda("z'", bound_var("z'")),
                              redex(bound_var("y"), bound_var("z")),
                          ),
            )),
            lambda("z", bound_var("z"))
        );

        let expected2 = lambda_no_box(
            "z",
            redex(
                lambda("z'", bound_var("z'")),
                redex(
                    lambda("z''", bound_var("z''")),
                    bound_var("z")
                ),
            ),
        );

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected1, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected2, expr);
    }

    #[test]
    fn several_stages2() {
        let expr = redex_no_box(
            redex(
                lambda("x",
                       lambda("y",
                              lambda("z",
                                     redex(
                                         redex(bound_var("x"), bound_var("z")),
                                         redex(bound_var("y"), bound_var("z")),
                                     ),
                ))),
                lambda("a", lambda("b", bound_var("a"))),
            ),
            lambda("c", lambda("d", bound_var("d"))),
        );

        let expected1 = redex_no_box(
            lambda("y",
                   lambda("z",
                          redex(
                              redex(
                                  lambda("a", lambda("b", bound_var("a"))),
                                  bound_var("z"),
                              ),
                              redex(bound_var("y"), bound_var("z")),
                          ),
            )),
            lambda("c", lambda("d", bound_var("d"))),
        );

        let expected2 = lambda_no_box(
            "z",
            redex(
                redex(
                    lambda("a", lambda("b", bound_var("a"))),
                    bound_var("z"),
                ),
                redex(
                    lambda("c", lambda("d", bound_var("d"))),
                    bound_var("z"),
                ),
            ),
        );

        let expected3 = lambda_no_box(
            "z",
            redex(
                lambda("b", bound_var("z")),
                redex(
                    lambda("c", lambda("d", bound_var("d"))),
                    bound_var("z"),
                ),
            ),
        );

        let expected4 = lambda_no_box("z", bound_var("z"));

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected1, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected2, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected3, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected4, expr);
    }
}
