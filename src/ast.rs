use std::fmt;
use std::fmt::{Display, Formatter};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expr {
    Var { name: String, is_free: bool, },
    LambdaTerm {var_name: String, body: Box<Expr>},
    Redex(Box<Expr>, Box<Expr>),
}

impl Expr {
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
    pub fn beta_reduce_print(self) -> Expr {
        self.beta_reduce(true)
    }

    /// Identical to beta_reduce_print() but doesn't print anything.
    pub fn beta_reduce_quiet(self) -> Expr {
        self.beta_reduce(false)
    }

    fn beta_reduce(mut self, should_print: bool) -> Expr {
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

    // Returns the expression after attemtping to apply a single beta-reduction,
    // and a boolean which is whether or not a reduction could be made.
    //
    fn beta_reduce_once(self, lambda_vars_in_use: &mut HashSet<String>) -> (Expr, bool) {
        match self {
            Expr::Redex(left, mut right) => {
                if let Expr::LambdaTerm {var_name, body: mut lambda_body} = *left {
                    // note that we don't include this lambda's var name in
                    // lambda_vars_in_use, since it's the variable that will
                    // be replaced by reduction
                    //
                    lambda_body.get_all_lambda_vars(lambda_vars_in_use);
                    right.alpha_convert(lambda_vars_in_use);
                    lambda_vars_in_use.clear();

                    lambda_body.replace_bound_var(&right, &var_name);
                    let new_expr = *lambda_body;
                    (new_expr, true)
                } else {
                    let (new_left, has_changed)
                        = left.beta_reduce_once(lambda_vars_in_use);
                    if has_changed {
                        let new_expr = Expr::Redex(Box::new(new_left), right);
                        return (new_expr, true);
                    }
                    let (new_right, has_changed)
                        = right.beta_reduce_once(lambda_vars_in_use);
                    let new_expr = Expr::Redex(
                        Box::new(new_left),
                        Box::new(new_right)
                    );
                    (new_expr, has_changed)
                }
            },
            Expr::LambdaTerm {var_name: name, body: lambda_body} => {
                //lambda_vars_in_use.insert(name.clone());

                let (new_body, has_changed)
                    = lambda_body.beta_reduce_once(lambda_vars_in_use);

                //lambda_vars_in_use.remove(&name);

                let new_lambda = Expr::LambdaTerm {
                    var_name: name,
                    body: Box::new(new_body),
                };
                (new_lambda, has_changed)
            },
            _ => (self, false),
        }
    }

    fn get_all_lambda_vars(&self, lambda_vars_in_use: &mut HashSet<String>) {
        match self {
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

    // FIXME change the names inside the lambdas too!
    fn alpha_convert(&mut self, lambda_vars_in_use: &mut HashSet<String>) {
        match self {
            Expr::LambdaTerm {var_name: name, body: lambda_body} => {
                loop {
                    if !lambda_vars_in_use.contains(name) {
                        lambda_vars_in_use.insert(name.clone());
                        lambda_body.alpha_convert(lambda_vars_in_use);
                        break;
                    }
                    name.push('\'');
                }
            },
            Expr::Redex(left, right) => {
                left.alpha_convert(lambda_vars_in_use);
                right.alpha_convert(lambda_vars_in_use);
            }
            _ => {},
        }
    }

    fn replace_bound_var(&mut self, arg: &Expr, var_name: &str) {
        match self {
            Expr::Redex(left, right) => {
                left.replace_bound_var(arg, var_name);
                right.replace_bound_var(arg, var_name);
            },
            Expr::LambdaTerm { var_name: _, body: lambda_body } => {
                lambda_body.replace_bound_var(arg, var_name);
            },
            Expr::Var{ name, is_free } => {
                if *is_free && var_name == name {
                    *self = arg.clone();
                }
            },
        };
    }

    pub fn substitute_symbols_from(&mut self, symbol_table: &HashMap<String, Expr>) {
        match self {
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
                    Some(expr) => *self = expr.clone(),
                };
            },
        }
    }

    fn actual_fmt(&self, f: &mut Formatter,
                  outer_term_is_lambda: bool) -> fmt::Result {
        match self {
            Expr::Redex(left, right) => {
                let mut right_paren_needed = false;
                if let Expr::Redex(_,_) = **right {
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
                match **lambda_body {
                    Expr::LambdaTerm {var_name: _, body: _} => {},
                    _ => write!(f, ". ")?,
                }

                if paren_needed {
                    write!(f, ")")?;
                }
            },
            Expr::Var { name, is_free: _ } => write!(f, "{}", name)?,
        }
        Ok(())
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.actual_fmt(f, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn not_redex1() {
        let expr = Expr::Var{ name: "a".to_string(), is_free: true };
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn not_redex2() {
        let expr = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::Var { name: "x".to_string(), is_free: false }),
        };
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn not_redex3() {
        let expr = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Var{name: "x".to_string(), is_free: false }),
                    Box::new(Expr::Var{name: "y".to_string(), is_free: false }),
                )),
            }),
        }; // lambda x . lambda y . x y
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn fake_redex1() {
        let expr = Expr::Redex(
            Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
            Box::new(Expr::Var{ name: "b".to_string(), is_free: true })
        ); // a b
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn fake_redex2() {
        let expr = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
                Box::new(Expr::Var{ name: "b".to_string(), is_free: true }),
            )),
            Box::new(Expr::Var { name: "c".to_string(), is_free: true }),
        ); // (a b) c
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn fake_redex3() {
        let expr = Expr::Redex(
            Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
            Box::new(Expr::Redex(
                Box::new(Expr::Var{ name: "b".to_string(), is_free: true }),
                Box::new(Expr::Var{ name: "c".to_string(), is_free: true }),
            )),
        ); // a (b c)
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn single_bound_var() {
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
            }),
            Box::new(Expr::Var {name: "a".to_string(), is_free: true }),
        ); // (lambda x . x) a
        let expected = Expr::Var{ name: "a".to_string(), is_free: true };

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);
        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn multiple_bound_vars() {
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body:
                    Box::new(Expr::Redex(
                        Box::new(Expr::Redex(
                            Box::new(Expr::Var { name: "x".to_string(), is_free: false }),
                            Box::new(Expr::Var { name: "x".to_string(), is_free: false }),
                        )),
                        Box::new(Expr::Var { name: "x".to_string(), is_free: false }),
                    )),
            }),
            Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
        ); // (lambda x . x x x) a
        let expected = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
                Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
            )),
            Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
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
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var{name: "a".to_string(), is_free: true}),
                        Box::new(Expr::Var{name: "x".to_string(), is_free: false}),
                    )),
                    Box::new(Expr::Var{ name: "b".to_string(), is_free: true }),
                )),
            }),
            Box::new(Expr::Var{ name: "c".to_string(), is_free:true }),
        ); // (lambda x . a x b) c
        let expected = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
                Box::new(Expr::Var{ name: "c".to_string(), is_free: true }),
            )),
            Box::new(Expr::Var{ name: "b".to_string(), is_free: true }),
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
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
            }),
        ); // (lambda x . x) (lambda y . y)
        let expected = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
        };

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);
        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn constant_lambda() {
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
            }),
            Box::new(Expr::Var{ name: "b".to_string(), is_free: true }),
        ); // (lambda x . a) b
        let expected = Expr::Var{ name: "a".to_string(), is_free: true };

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn nested_lambdas() {
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "y".to_string(),
                    body: Box::new(Expr::Redex(
                        Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                        Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
                    )),
                }),
            }),
            Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
        ); // (lambda x . lambda y . x y) a

        let expected = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::Redex(
                Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
                Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
            )),
        };

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);
        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn nested_lambdas_multilevel_subst() {
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                        Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
                    )),
                    Box::new(Expr::LambdaTerm {
                        var_name: "y".to_string(),
                        body: Box::new(Expr::Redex(
                            Box::new(Expr::Redex(
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var { name: "x".to_string(), is_free: false }),
                                    Box::new(Expr::Var { name: "y".to_string(), is_free: false }),
                                )),
                                Box::new(Expr::Var { name: "a".to_string(), is_free: true }),
                            )),
                            Box::new(Expr::LambdaTerm {
                                var_name: "z".to_string(),
                                body: Box::new(Expr::Redex(
                                    Box::new(Expr::Redex(
                                        Box::new(Expr::Redex(
                                            Box::new(Expr::Var { name: "x".to_string(), is_free: false }),
                                            Box::new(Expr::Var { name: "y".to_string(), is_free: false }),
                                        )),
                                        Box::new(Expr::Var { name: "z".to_string(), is_free: false }),
                                    )),
                                    Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
                                )),
                            }),
                        )),
                    }),
                )),
            }),
            Box::new(Expr::Var{ name: "b".to_string(), is_free: true }),
        ); // (lambda x . x a (lambda y . x y a (lambda z . x y z a))) b

        let expected = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::Var{ name: "b".to_string(), is_free: true }),
                Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
            )),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Redex(
                            Box::new(Expr::Var{ name: "b".to_string(), is_free: true }),
                            Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
                        )),
                        Box::new(Expr::Var{ name: "a".to_string(), is_free: true }),
                    )),
                    Box::new(Expr::LambdaTerm {
                        var_name: "z".to_string(),
                        body: Box::new(Expr::Redex(
                            Box::new(Expr::Redex(
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var{name: "b".to_string(), is_free: true}),
                                    Box::new(Expr::Var{name: "y".to_string(), is_free: false}),
                                )),
                                Box::new(Expr::Var{name: "z".to_string(), is_free: false}),
                            )),
                            Box::new(Expr::Var{name: "a".to_string(), is_free: true}),
                        )),
                    }),
                )),
            }),
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
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                    Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                )),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                    Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                )),
            }),
        ); // (lambda x . x x) (lambda x . x x)
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn two_stage_normal_order() {
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
            }),
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "y".to_string(),
                    body: Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
                }),
                Box::new(Expr::Var{name: "a".to_string(), is_free: true}),
            )),
        ); // (lambda x . x) ((lambda y . y) a)
        let expected1 = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
            }),
            Box::new(Expr::Var{name: "a".to_string(), is_free: true}),
        );
        let expected2 = Expr::Var{name: "a".to_string(), is_free: true};

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
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                    Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                )),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
            }),
        ); // (lambda x . x x) (lambda y . y)
        let expected1 = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body:Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body:Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
            }),
        );
        let expected2 = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
        };

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
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Var{name: "a".to_string(), is_free: true}),
            }),
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::Redex(
                        Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                        Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                    )),
                }),
                Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::Redex(
                        Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                        Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                    )),
                }),
            )),
        );
        let expected = Expr::Var{name: "a".to_string(), is_free: true};

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn reduction_inside_lambda_body() {
        let expr = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "a".to_string(),
                    body: Box::new(Expr::Var{ name: "a".to_string(), is_free: false }),
                }),
                Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
            )),
        }; // lambda x . ((lambda a . a) x)
        let expected = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
        };
        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn dont_recapture_bound_var() {
        let expr = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "a".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "b".to_string(),
                        body: Box::new(Expr::Var{ name: "a".to_string(), is_free: false }),
                    }),
                }),
                Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
            )),
        }; // \x -> ((\a b -> a) x)

        let expected = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::LambdaTerm {
                var_name: "b".to_string(),
                body: Box::new(Expr::Var {name: "x".to_string(), is_free: false }),
            }),
        }; // \x -> \b -> x

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn alpha_conversion() {
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "y".to_string(),
                    body: Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                }),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var { name: "y".to_string(), is_free: false }),
            }),
        ); // (\x y -> x) (\y -> y)

        // should reduce to \y y' -> y' but may reduce to \y y -> y if alpha
        // conversion is not being done properly

        let expected = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::LambdaTerm {
                var_name: "y'".to_string(),
                body: Box::new(Expr::Var{ name: "y'".to_string(), is_free: false }),
            }),
        };

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(has_changed);
        assert_eq!(expected, expr);

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn several_stages() {
        let expr = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::LambdaTerm {
                        var_name: "x".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "y".to_string(),
                            body: Box::new(Expr::LambdaTerm {
                                var_name: "z".to_string(),
                                body: Box::new(Expr::Redex(
                                    Box::new(Expr::Redex(
                                        Box::new(Expr::Var{ name: "x".to_string(), is_free: false }),
                                        Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                                    )),
                                    Box::new(Expr::Redex(
                                        Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
                                        Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                                    )),
                                )),
                            }),
                        }),
                    }),
                    Box::new(Expr::LambdaTerm {
                        var_name: "a".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "b".to_string(),
                            body: Box::new(Expr::Var{ name: "a".to_string(), is_free: false }),
                        }),
                    }),
                )),
                Box::new(Expr::LambdaTerm {
                    var_name: "c".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "d".to_string(),
                        body: Box::new(Expr::Var{ name: "c".to_string(), is_free: false }),
                    }),
                }),
            )),
            Box::new(Expr::Var{name: "n".to_string(), is_free: true}),
        ); // (\x y z -> x z (y z)) (\a b -> a) (\c d -> d) n    -- OR: S K K a

        let expected1 = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "y".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "z".to_string(),
                        body: Box::new(Expr::Redex(
                            Box::new(Expr::Redex(
                                Box::new(Expr::LambdaTerm {
                                    var_name: "a".to_string(),
                                    body: Box::new(Expr::LambdaTerm {
                                        var_name: "b".to_string(),
                                        body: Box::new(Expr::Var{ name: "a".to_string(), is_free: false }),
                                    }),
                                }),
                                Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                            )),
                            Box::new(Expr::Redex(
                                Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
                                Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                            )),
                        )),
                    }),
                }),
                Box::new(Expr::LambdaTerm {
                    var_name: "c".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "d".to_string(),
                        body: Box::new(Expr::Var{ name: "c".to_string(), is_free: false }),
                    }),
                }),
            )),
            Box::new(Expr::Var{name: "n".to_string(), is_free: true}),
        );

        let expected2 = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "z".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::LambdaTerm {
                            var_name: "a".to_string(),
                            body: Box::new(Expr::LambdaTerm {
                                var_name: "b".to_string(),
                                body: Box::new(Expr::Var{ name: "a".to_string(), is_free: false }),
                            }),
                        }),
                        Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                    )),
                    Box::new(Expr::Redex(
                        Box::new(Expr::LambdaTerm {
                            var_name: "c".to_string(),
                            body: Box::new(Expr::LambdaTerm {
                                var_name: "d".to_string(),
                                body: Box::new(Expr::Var{ name: "c".to_string(), is_free: false }),
                            }),
                        }),
                        Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                    )),
                )),
            }),
            Box::new(Expr::Var{name: "n".to_string(), is_free: true}),
        );
        let expected3 = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "a".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "b".to_string(),
                        body: Box::new(Expr::Var { name: "a".to_string(), is_free: false }),
                    }),
                }),
                Box::new(Expr::Var{name: "n".to_string(), is_free: true}),
            )),
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "c".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "d".to_string(),
                        body: Box::new(Expr::Var { name: "c".to_string(), is_free: false }),
                    }),
                }),
                Box::new(Expr::Var{name: "n".to_string(), is_free: true}),
            )),
        );

        let expected4 = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "b".to_string(),
                body: Box::new(Expr::Var{name: "n".to_string(), is_free: true}),
            }),
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "c".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "d".to_string(),
                        body: Box::new(Expr::Var { name: "c".to_string(), is_free: false }),
                    }),
                }),
                Box::new(Expr::Var{name: "n".to_string(), is_free: true}),
            )),
        );

        let expected5 = Expr::Var{name: "n".to_string(), is_free: true};

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
    fn several_stages2() {
        let expr = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "y".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "z".to_string(),
                            body: Box::new(Expr::Redex(
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var { name: "x".to_string(), is_free: true }),
                                    Box::new(Expr::Var { name: "z".to_string(), is_free: true }),
                                )),
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var { name: "y".to_string(), is_free: true }),
                                    Box::new(Expr::Var { name: "z".to_string(), is_free: true }),
                                )),
                            )),
                        }),
                    }),
                }),
                Box::new(Expr::LambdaTerm {
                    var_name: "a".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "b".to_string(),
                        body: Box::new(Expr::Var { name: "a".to_string(), is_free: true }),
                    }),
                }),
            )),
            Box::new(Expr::LambdaTerm {
                var_name: "c".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "d".to_string(),
                    body: Box::new(Expr::Var { name: "c".to_string(), is_free: true }),
                }),
            }),
        ); // (\x y z -> x z (y z)) (\a b -> a) (\c d -> d)     -- OR: S K K

        let expected1 = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "z".to_string(),
                    body: Box::new(Expr::Redex(
                        Box::new(Expr::Redex(
                            Box::new(Expr::LambdaTerm {
                                var_name: "a".to_string(),
                                body: Box::new(Expr::LambdaTerm {
                                    var_name: "b".to_string(),
                                    body: Box::new(Expr::Var{ name: "a".to_string(), is_free: false }),
                                }),
                            }),
                            Box::new(Expr::Var{ name: "z".to_string(), is_free: false}),
                        )),
                        Box::new(Expr::Redex(
                            Box::new(Expr::Var{ name: "y".to_string(), is_free: false }),
                            Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                        )),
                    )),
                }),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "c".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "d".to_string(),
                    body: Box::new(Expr::Var{ name: "c".to_string(), is_free: false }),
                }),
            }),
        );
        let expected2 = Expr::LambdaTerm {
            var_name: "z".to_string(),
            body: Box::new(Expr::Redex(
                Box::new(Expr::Redex(
                    Box::new(Expr::LambdaTerm {
                        var_name: "a".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "b".to_string(),
                            body: Box::new(Expr::Var{ name: "a".to_string(), is_free: false }),
                        }),
                    }),
                    Box::new(Expr::Var{ name: "".to_string(), is_free: false }),
                )),
                Box::new(Expr::Redex(
                    Box::new(Expr::LambdaTerm {
                        var_name: "c".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "d".to_string(),
                            body: Box::new(Expr::Var { name: "c".to_string(), is_free: false }),
                        }),
                    }),
                    Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                )),
            )),
        };
        let expected3 = Expr::LambdaTerm {
            var_name: "z".to_string(),
            body: Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "b".to_string(),
                    body: Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                }),
                Box::new(Expr::Redex(
                    Box::new(Expr::LambdaTerm {
                        var_name: "c".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "d".to_string(),
                            body: Box::new(Expr::Var{ name: "c".to_string(), is_free: false }),
                        }),
                    }),
                    Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
                )),
            )),
        };

        let expected4 = Expr::LambdaTerm {
            var_name: "z".to_string(),
            body: Box::new(Expr::Var{ name: "z".to_string(), is_free: false }),
        };

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
