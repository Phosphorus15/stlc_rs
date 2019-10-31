use std::collections::HashMap;
use crate::Name::Local;

#[derive(Clone, Eq, PartialEq, Debug, Hash)]
enum Name {
    Global(String),
    Local(usize),
    Quote(usize),
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum Type {
    Free(Name),
    Fun(Box<Self>, Box<Self>),
    Bot,
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum InferTerm {
    Ann(Term, Type),
    Free(Name),
    Bound(usize),
    App(Box<Self>, Term),
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum Term {
    Inf(Box<InferTerm>),
    Lam(Box<Self>),
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum Value {
    Lam(Term, BoundVar),
    Neutral(Neutral),
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum Neutral {
    Free(Name),
    App(Box<Self>, Box<Value>),
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum ContextInfo {
    Kind,
    Type(Type),
}

type BoundVar = Vec<Value>;

type TypeContext = HashMap<Name, ContextInfo>;

fn eval_infer(term: InferTerm, env: BoundVar) -> Value {
    match term {
        InferTerm::Free(name) => Value::Neutral(
            Neutral::Free(name)
        ),
        InferTerm::Bound(v) => {
            println!("bound vars {:?}", env);
            env[env.len() - v - 1].clone()
        }
        InferTerm::Ann(t, _) => {
            eval(t, env.clone())
        }
        InferTerm::App(t1, t2) => {
            let v1 = eval_infer(*t1, env.clone());
            let v2 = eval(t2, env.clone());
            match v1 {
                Value::Lam(t, mut lenv) => {
                    lenv.push(v2);
                    eval(t, lenv)
                }
                Value::Neutral(neutral) => {
                    Value::Neutral(
                        Neutral::App(Box::new(neutral), Box::new(v2))
                    )
                }
            }
        }
    }
}

fn eval(term: Term, env: BoundVar) -> Value {
    match term {
        Term::Inf(infer) => eval_infer(*infer, env.clone()),
        Term::Lam(body) => {
            Value::Lam(*body, env.clone())
        }
    }
}

fn valid_ty(ty: &Type, context: &TypeContext) -> bool {
    match ty {
        Type::Fun(l, r) => valid_ty(&*l, context) || valid_ty(&*r, context),
        Type::Free(name) => context.contains_key(&name),
        _ => false
    }
}

fn type_infer(term: InferTerm, context: TypeContext, index: usize) -> Result<Type, String> {
    match term {
        InferTerm::Free(name) => context.get(&name)
            .iter().filter_map(|v| {
            match v {
                ContextInfo::Type(ty) => Some(ty),
                _ => None
            }
        }).last().cloned().ok_or(format!("Type mismatched for {:?}", name)),
        InferTerm::Bound(_) => {
            Err("Unbound lambda vars".to_string())
        }
        InferTerm::App(t1, t2) => {
            match type_infer(*t1, context.clone(), index) {
                Ok(Type::Fun(ty1, ty2)) => {
                    type_check(t2, *ty1, context, index).map(|_| *ty2)
                }
                Ok(ty) => Err(format!("Illegal application to type: {:?}", ty)),
                Err(msg) => Err(format!("Illegal application: {:?}", msg)),
            }
        }
        InferTerm::Ann(t, ty) => {
            if valid_ty(&ty, &context) {
                type_check(t, ty.clone(), context, index).map(|_| ty)
            } else {
                Err(format!("Invalid type annotation: {:?}", ty))
            }
        }
    }
}

fn type_check(term: Term, ty: Type, mut context: TypeContext, index: usize) -> Result<(), String> {
    match term {
        Term::Inf(inf) => {
            match type_infer(*inf, context, index) {
                Ok(tyi) => if tyi == ty {
                    Ok(())
                } else {
                    Err("Mismatched types".to_string())
                },
                Err(err) => Err(err)
            }
        }
        Term::Lam(body) => {
            match ty {
                Type::Fun(l, r) => {
                    let typ = subst(InferTerm::Free(Name::Local(index)), *body, index);
                    context.insert(Local(index), ContextInfo::Type(*l));
                    type_check(typ, *r, context, index + 1)
                }
                _ => Err("Incorrect type prediction for lambda abstraction".to_string())
            }
        }
    }
}

fn subst_infer(s: InferTerm, t: InferTerm, index: usize) -> InferTerm {
    match t {
        InferTerm::Bound(i) =>
            if i == index {
                s
            } else {
                InferTerm::Bound(i)
            },
        InferTerm::Ann(t, ty) => InferTerm::Ann(subst(s, t, index), ty),
        InferTerm::App(l, r) => InferTerm::App(
            Box::new(subst_infer(s.clone(), *l, index)), subst(s, r, index),
        ),
        _ => t
    }
}

fn subst(s: InferTerm, t: Term, index: usize) -> Term {
    match t {
        Term::Lam(body) => Term::Lam(
            Box::new(
                subst(s, *body, index + 1)
            )
        ),
        Term::Inf(inf) => Term::Inf(
            Box::new(
                subst_infer(s, *inf, index)
            )
        )
    }
}

fn main() {
    let mut context = HashMap::new();
    context.insert(Name::Global("a".to_string()), ContextInfo::Kind);
    let id = Term::Lam(
        Box::new(
            Term::Inf(
                Box::new(
                    InferTerm::Bound(0)
                )
            )
        )
    );
    let id_sign = Box::new(
        Type::Fun(
            Box::new(
                Type::Free(Name::Global("a".to_string()))
            ),
            Box::new(
                Type::Free(Name::Global("a".to_string()))
            ),
        )
    );
    let type_sign = Type::Fun(
        id_sign.clone(),
        id_sign,
    );
    let expr = InferTerm::App(
        Box::new(
            InferTerm::Ann(
                id.clone(),
                type_sign.clone(), // totally untyped
            )
        ),
        id.clone(),
    );
    println!("{:?}", eval_infer(expr.clone(), vec![]));
    println!("{:?}", type_infer(expr, context.clone(), 0));
}

#[test]
fn ty_check_pass() {
    let mut context = HashMap::new();
    context.insert(Name::Global("a".to_string()), ContextInfo::Kind);
    let id = Term::Lam(
        Box::new(
            Term::Inf(
                Box::new(
                    InferTerm::Bound(0)
                )
            )
        )
    );
    let id_sign = Box::new(
        Type::Fun(
            Box::new(
                Type::Free(Name::Global("a".to_string()))
            ),
            Box::new(
                Type::Free(Name::Global("a".to_string()))
            ),
        )
    );
    let type_sign = Type::Fun(
        id_sign.clone(),
        id_sign,
    );
    let expr = InferTerm::App(
        Box::new(
            InferTerm::Ann(
                id.clone(),
                type_sign.clone(), // totally untyped
            )
        ),
        id.clone(),
    );
    assert!(type_infer(expr, context.clone(), 0).is_ok());
}

#[test]
fn ty_check_fail() {
    let mut context = HashMap::new();
    context.insert(Name::Global("a".to_string()), ContextInfo::Kind);
    let id = Term::Lam(
        Box::new(
            Term::Inf(
                Box::new(
                    InferTerm::Bound(0)
                )
            )
        )
    );
    let constv = Term::Lam(
        Box::new(
            Term::Lam(
                Box::new(
                    Term::Inf(
                        Box::new(
                            InferTerm::Bound(1)
                        )
                    )
                )
            )
        )
    );
    let expr = InferTerm::App(
        Box::new(
            InferTerm::Ann(
                id.clone(),
                Type::Bot, // totally untyped
            )
        ),
        id.clone(),
    );
    let expr2 = InferTerm::App(
        Box::new(
            expr.clone()
        ),
        constv.clone(),
    );
    assert!(type_infer(expr2, context.clone(), 0).is_err());
}
