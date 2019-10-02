use std::fmt;
use std::fmt::{Display, Formatter};
use std::collections::{HashMap, HashSet};

// FIXME: there's a bug on the reduction. This
/*
> I = \a -> a
> K = \b c -> b
> S = \x y z -> x z (y z)
> S K K
= (λx y z. x z (y z)) (λb c. b) (λb c. b)
= (λy z. (λb c. b) z (y z)) (λb c. b)
= (λz. (λb c. b) z ((λb c. b) z))
= (λz. (λc. c) ((λb c. b) z))           -- wrong! Should have been (λc. z)
= (λz. (λb c. b) z)
= (λz c. c)
*/
// ...yields the incorrect where shown, which propagates to the wrong result
// till the end, but weirdly enough, copy-pasting that line and running it
// gives the right result:
/*
> (λz. (λb c. b) z ((λb c. b) z))
= (λz. (λb c. b) z ((λb c. b) z))
= (λz. (λc. z) ((λb c. b) z))
= (λz. z)
*/
//
// The conclusion is in several_stages2().
// Should we give up using de bruijn indexes? If we did this wouldn't happen,
// plus we already have to alpha reduce vars anyway.
// Otherwise, we'd have to recalculate the number of bound vars on the following
// circumstances:
// - on the right, we have a bound var whose index is greater than the depth
// of lambdas we have (i.e. a var bound to a lambda that's external to the redex);
// - on the left, we have an expression that has more two or more nested lambdas.
// The number of the bound var (on the right expr) is, in every location,
// incremented of the depth of lambdas of the term on the left where BoundVar(1)
// (the one that will be replaced) happens minus 1 because of the var we're
// going to substitute.
//

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Var {
    BoundVar(usize),    // de Brujin index
    FreeVar(String),    // free vars can't be renamed; store their names instead
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expr {
    Var(Var),
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
    /// assert_eq!(non_redex, Expr::Var(Var::FreeVar("a".to_string())));
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
                if let Expr::LambdaTerm {var_name: _, body: mut lambda_body} = *left {
                    // note that we don't include this lambda's var name in
                    // lambda_vars_in_use, since it's the variable that will
                    // be replaced by reduction
                    //
                    lambda_body.get_all_lambda_vars(lambda_vars_in_use);
                    right.alpha_convert(lambda_vars_in_use);
                    lambda_vars_in_use.clear();

                    lambda_body.replace_bound_var(&right, 1);
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

    // TODO while we're at it, we should do something about avoid recapturing
    // bound vars too
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

    fn replace_bound_var(&mut self, arg: &Expr, index: usize) {
        match self {
            Expr::Redex(left, right) => {
                left.replace_bound_var(arg, index);
                right.replace_bound_var(arg, index);
            },
            Expr::LambdaTerm { var_name: _, body: lambda_body } => {
                lambda_body.replace_bound_var(arg, index + 1);
            },
            Expr::Var(var) => if let Var::BoundVar(i) = var {
                if *i == index {
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
            Expr::Var(var) => if let Var::FreeVar(name) = var {
                match symbol_table.get(name) {
                    None => return,
                    Some(expr) => *self = expr.clone(),
                };
            }
        }
    }

    // As in LineParser, lambda_vars' index is the inverse de Brujin index.
    fn actual_fmt(&self, f: &mut Formatter,
                  lambda_vars: &mut Vec<String>,
                  outer_term_is_lambda: bool) -> fmt::Result {
        match self {
            Expr::Redex(left, right) => {
                let mut right_paren_needed = false;
                if let Expr::Redex(_,_) = **right {
                    right_paren_needed = true;
                }

                left.actual_fmt(f, lambda_vars, false)?;
                write!(f, " ")?;

                if right_paren_needed {
                    write!(f, "(")?;
                }
                right.actual_fmt(f, lambda_vars, false)?;
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

                lambda_vars.push(name.to_string());
                lambda_body.actual_fmt(f, lambda_vars, true)?;
                lambda_vars.pop();

                if paren_needed {
                    write!(f, ")")?;
                }
            },
            Expr::Var(var) => match var {
                Var::BoundVar(i) => {
                    match lambda_vars.get(lambda_vars.len() - i) {
                        Some(s) => write!(f, "{}", s)?,
                        None => return Err(fmt::Error),
                    }
                },
                Var::FreeVar(s) => write!(f, "{}", s)?,
            },
        }
        Ok(())
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut lambda_vars = Vec::new();
        self.actual_fmt(f, &mut lambda_vars, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn not_redex1() {
        let expr = Expr::Var(Var::FreeVar("a".to_string()));
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn not_redex2() {
        let expr = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::Var(Var::BoundVar(1))),
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
                    Box::new(Expr::Var(Var::BoundVar(2))),
                    Box::new(Expr::Var(Var::BoundVar(1))),
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
            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
            Box::new(Expr::Var(Var::FreeVar("b".to_string())))
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
                Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                Box::new(Expr::Var(Var::FreeVar("b".to_string())))
            )),
            Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
        ); // (a b) c
        let expected = expr.clone();

        let (expr, has_changed) = expr.beta_reduce_once(&mut HashSet::new());
        assert!(!has_changed);
        assert_eq!(expected, expr);
    }

    #[test]
    fn fake_redex3() {
        let expr = Expr::Redex(
            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
            Box::new(Expr::Redex(
                Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
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
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
        ); // (lambda x . x) a
        let expected = Expr::Var(Var::FreeVar("a".to_string()));

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
                            Box::new(Expr::Var(Var::BoundVar(1))),
                            Box::new(Expr::Var(Var::BoundVar(1))),
                        )),
                        Box::new(Expr::Var(Var::BoundVar(1))),
                    )),
            }),
            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
        ); // (lambda x . x x x) a
        let expected = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
            )),
            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
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
                        Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                        Box::new(Expr::Var(Var::BoundVar(1))),
                    )),
                    Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                )),
            }),
            Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
        ); // (lambda x . a x b) c
        let expected = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                Box::new(Expr::Var(Var::FreeVar("c".to_string()))),
            )),
            Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
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
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
        ); // (lambda x . x) (lambda y . y)
        let expected = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::Var(Var::BoundVar(1))),
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
                body: Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
            }),
            Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
        ); // (lambda x . a) b
        let expected = Expr::Var(Var::FreeVar("a".to_string()));

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
                        Box::new(Expr::Var(Var::BoundVar(2))),
                        Box::new(Expr::Var(Var::BoundVar(1))),
                    )),
                }),
            }),
            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
        ); // (lambda x . lambda y . x y) a

        let expected = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::Redex(
                Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                Box::new(Expr::Var(Var::BoundVar(1))),
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
                        Box::new(Expr::Var(Var::BoundVar(1))),
                        Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                    )),
                    Box::new(Expr::LambdaTerm {
                        var_name: "y".to_string(),
                        body: Box::new(Expr::Redex(
                            Box::new(Expr::Redex(
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var(Var::BoundVar(2))),
                                    Box::new(Expr::Var(Var::BoundVar(1))),
                                )),
                                Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                            )),
                            Box::new(Expr::LambdaTerm {
                                var_name: "z".to_string(),
                                body: Box::new(Expr::Redex(
                                    Box::new(Expr::Redex(
                                        Box::new(Expr::Redex(
                                            Box::new(Expr::Var(Var::BoundVar(3))),
                                            Box::new(Expr::Var(Var::BoundVar(2))),
                                        )),
                                        Box::new(Expr::Var(Var::BoundVar(1))),
                                    )),
                                    Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                                )),
                            }),
                        )),
                    }),
                )),
            }),
            Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
        ); // (lambda x . x a (lambda y . x y a (lambda z . x y z a))) b

        let expected = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
            )),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Redex(
                        Box::new(Expr::Redex(
                            Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                            Box::new(Expr::Var(Var::BoundVar(1))),
                        )),
                        Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
                    )),
                    Box::new(Expr::LambdaTerm {
                        var_name: "z".to_string(),
                        body: Box::new(Expr::Redex(
                            Box::new(Expr::Redex(
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var(Var::FreeVar("b".to_string()))),
                                    Box::new(Expr::Var(Var::BoundVar(2))),
                                )),
                                Box::new(Expr::Var(Var::BoundVar(1))),
                            )),
                            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
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
                    Box::new(Expr::Var(Var::BoundVar(1))),
                    Box::new(Expr::Var(Var::BoundVar(1))),
                )),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::Redex(
                    Box::new(Expr::Var(Var::BoundVar(1))),
                    Box::new(Expr::Var(Var::BoundVar(1))),
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
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "y".to_string(),
                    body: Box::new(Expr::Var(Var::BoundVar(1))),
                }),
                Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
            )),
        ); // (lambda x . x) ((lambda y . y) a)
        let expected1 = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
            Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
        );
        let expected2 = Expr::Var(Var::FreeVar("a".to_string()));

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
                    Box::new(Expr::Var(Var::BoundVar(1))),
                    Box::new(Expr::Var(Var::BoundVar(1))),
                )),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
        ); // (lambda x . x x) (lambda y . y)
        let expected1 = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
        );
        let expected2 = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::Var(Var::BoundVar(1))),
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
                body: Box::new(Expr::Var(Var::FreeVar("a".to_string()))),
            }),
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::BoundVar(1))),
                        Box::new(Expr::Var(Var::BoundVar(1))),
                    )),
                }),
                Box::new(Expr::LambdaTerm {
                    var_name: "x".to_string(),
                    body: Box::new(Expr::Redex(
                        Box::new(Expr::Var(Var::BoundVar(1))),
                        Box::new(Expr::Var(Var::BoundVar(1))),
                    )),
                }),
            )),
        );
        let expected = Expr::Var(Var::FreeVar("a".to_string()));

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
                    body: Box::new(Expr::Var(Var::BoundVar(1))),
                }),
                Box::new(Expr::Var(Var::BoundVar(1))),
            )),
        }; // lambda x . ((lambda a . a) x)
        let expected = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::Var(Var::BoundVar(1))),
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
                        body: Box::new(Expr::Var(Var::BoundVar(2))),
                    }),
                }),
                Box::new(Expr::Var(Var::BoundVar(1))),
            )),
        }; // \x -> ((\a b -> a) x)

        // Should become \x -> (\b -> x) but may become \x -> (\b -> b) due
        // to the bound variable being represented only as BoundVar(1)
        // which means "b" under the new lamda term, i.e. the var has been
        // re-captured.
        // (FIXME like what's happening right now...)

        let expected = Expr::LambdaTerm {
            var_name: "x".to_string(),
            body: Box::new(Expr::LambdaTerm {
                var_name: "b".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(2))),
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
    fn alpha_conversion() {
        let expr = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "x".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "y".to_string(),
                    body: Box::new(Expr::Var(Var::BoundVar(2))),
                }),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "y".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1))),
            }),
        ); // (\x y -> x) (\y -> y)

        // should reduce to \y y' -> y' but may reduce to \y y -> y if alpha
        // conversion is not being done properly

        let expected = Expr::LambdaTerm {
            var_name: "y".to_string(),
            body: Box::new(Expr::LambdaTerm {
                var_name: "y'".to_string(),
                body: Box::new(Expr::Var(Var::BoundVar(1))),
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
                                        Box::new(Expr::Var(Var::BoundVar(3))),
                                        Box::new(Expr::Var(Var::BoundVar(1))),
                                    )),
                                    Box::new(Expr::Redex(
                                        Box::new(Expr::Var(Var::BoundVar(2))),
                                        Box::new(Expr::Var(Var::BoundVar(1))),
                                    )),
                                )),
                            }),
                        }),
                    }),
                    Box::new(Expr::LambdaTerm {
                        var_name: "a".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "b".to_string(),
                            body: Box::new(Expr::Var(Var::BoundVar(2))),
                        }),
                    }),
                )),
                Box::new(Expr::LambdaTerm {
                    var_name: "c".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "d".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(2))),
                    }),
                }),
            )),
            Box::new(Expr::Var(Var::FreeVar("n".to_string()))),
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
                                        body: Box::new(Expr::Var(Var::BoundVar(2))),
                                    }),
                                }),
                                Box::new(Expr::Var(Var::BoundVar(1))),
                            )),
                            Box::new(Expr::Redex(
                                Box::new(Expr::Var(Var::BoundVar(2))),
                                Box::new(Expr::Var(Var::BoundVar(1))),
                            )),
                        )),
                    }),
                }),
                Box::new(Expr::LambdaTerm {
                    var_name: "c".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "d".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(2))),
                    }),
                }),
            )),
            Box::new(Expr::Var(Var::FreeVar("n".to_string()))),
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
                                body: Box::new(Expr::Var(Var::BoundVar(2))),
                            }),
                        }),
                        Box::new(Expr::Var(Var::BoundVar(1))),
                    )),
                    Box::new(Expr::Redex(
                        Box::new(Expr::LambdaTerm {
                            var_name: "c".to_string(),
                            body: Box::new(Expr::LambdaTerm {
                                var_name: "d".to_string(),
                                body: Box::new(Expr::Var(Var::BoundVar(2))),
                            }),
                        }),
                        Box::new(Expr::Var(Var::BoundVar(1))),
                    )),
                )),
            }),
            Box::new(Expr::Var(Var::FreeVar("n".to_string()))),
        );
        let expected3 = Expr::Redex(
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "a".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "b".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(2))),
                    }),
                }),
                Box::new(Expr::Var(Var::FreeVar("n".to_string()))),
            )),
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "c".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "d".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(2))),
                    }),
                }),
                Box::new(Expr::Var(Var::FreeVar("n".to_string()))),
            )),
        );

        let expected4 = Expr::Redex(
            Box::new(Expr::LambdaTerm {
                var_name: "b".to_string(),
                body: Box::new(Expr::Var(Var::FreeVar("n".to_string()))),
            }),
            Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "c".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "d".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(2))),
                    }),
                }),
                Box::new(Expr::Var(Var::FreeVar("n".to_string()))),
            )),
        );

        let expected5 = Expr::Var(Var::FreeVar("n".to_string()));

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
                                    Box::new(Expr::Var(Var::BoundVar(3))),
                                    Box::new(Expr::Var(Var::BoundVar(1))),
                                )),
                                Box::new(Expr::Redex(
                                    Box::new(Expr::Var(Var::BoundVar(2))),
                                    Box::new(Expr::Var(Var::BoundVar(1))),
                                )),
                            )),
                        }),
                    }),
                }),
                Box::new(Expr::LambdaTerm {
                    var_name: "a".to_string(),
                    body: Box::new(Expr::LambdaTerm {
                        var_name: "b".to_string(),
                        body: Box::new(Expr::Var(Var::BoundVar(2))),
                    }),
                }),
            )),
            Box::new(Expr::LambdaTerm {
                var_name: "c".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "d".to_string(),
                    body: Box::new(Expr::Var(Var::BoundVar(2))),
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
                                    body: Box::new(Expr::Var(Var::BoundVar(2))),
                                }),
                            }),
                            Box::new(Expr::Var(Var::BoundVar(1))),
                        )),
                        Box::new(Expr::Redex(
                            Box::new(Expr::Var(Var::BoundVar(2))),
                            Box::new(Expr::Var(Var::BoundVar(1))),
                        )),
                    )),
                }),
            }),
            Box::new(Expr::LambdaTerm {
                var_name: "c".to_string(),
                body: Box::new(Expr::LambdaTerm {
                    var_name: "d".to_string(),
                    body: Box::new(Expr::Var(Var::BoundVar(2))),
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
                            body: Box::new(Expr::Var(Var::BoundVar(2))),
                        }),
                    }),
                    Box::new(Expr::Var(Var::BoundVar(1))),
                )),
                Box::new(Expr::Redex(
                    Box::new(Expr::LambdaTerm {
                        var_name: "c".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "d".to_string(),
                            body: Box::new(Expr::Var(Var::BoundVar(2))),
                        }),
                    }),
                    Box::new(Expr::Var(Var::BoundVar(1))),
                )),
            )),
        };
        let expected3 = Expr::LambdaTerm {
            var_name: "z".to_string(),
            body: Box::new(Expr::Redex(
                Box::new(Expr::LambdaTerm {
                    var_name: "b".to_string(),
                    // XXX here is the problem.
                    // When we replace by BoundVar(1) the bound var
                    // becomes "a" even though it was originally
                    // meant to refer to z.
                    // XXX
                    body: Box::new(Expr::Var(Var::BoundVar(1))),
                }),
                Box::new(Expr::Redex(
                    Box::new(Expr::LambdaTerm {
                        var_name: "c".to_string(),
                        body: Box::new(Expr::LambdaTerm {
                            var_name: "d".to_string(),
                            body: Box::new(Expr::Var(Var::BoundVar(2))),
                        }),
                    }),
                    Box::new(Expr::Var(Var::BoundVar(1))),
                )),
            )),
        };

        let expected4 = Expr::LambdaTerm {
            var_name: "z".to_string(),
            body: Box::new(Expr::Var(Var::BoundVar(1))),
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
