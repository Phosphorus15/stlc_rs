use std::collections::HashMap;
use crate::Name::Local;
use crate::Value::VPi;
use crate::InferTerm::Free;

/// We implement this using a mixing of Named Variables (Whatever its type) and De brujin Indices
#[derive(Clone, Eq, PartialEq, Debug, Hash)]
enum Name {
    Global(String),
    Local(usize),
    Quote(usize),
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum InferTerm {
    Ann(Term, Term),
    Set,
    Pi(Term, Term),
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
    VSet,
    VPi(Box<Self>, Term, BoundVar),
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

type Type = Value;

type BoundVar = Vec<Value>;

type TypeContext = HashMap<Name, Type>;

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
            eval(t, env)
        }
        InferTerm::App(t1, t2) => {
            let v1 = eval_infer(*t1, env.clone());
            let v2 = eval(t2, env);
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
                _ => unreachable!("Illegal application")
            }
        }
        InferTerm::Set => Value::VSet,
        InferTerm::Pi(x, t) => VPi(Box::new(eval(x, env.clone())), t, env)
    }
}

fn eval(term: Term, env: BoundVar) -> Value {
    match term {
        Term::Inf(infer) => eval_infer(*infer, env),
        Term::Lam(body) => {
            Value::Lam(*body, env)
        }
    }
}

fn type_infer(term: InferTerm, mut context: TypeContext, index: usize) -> Result<Type, String> {
    match term {
        InferTerm::Free(name) => context.get(&name).cloned().ok_or(format!("Type mismatched for {:?}", name)),
        InferTerm::Bound(_) => {
            Err("Unbound lambda vars".to_string())
        }
        InferTerm::App(t1, t2) => {
            match type_infer(*t1, context.clone(), index) {
                Ok(Type::VPi(ty1, ty2, mut ctx)) => {
                    if type_check(t2.clone(), *ty1, context, index).is_ok() {
                        ctx.push(eval(t2, vec![]));
                        Ok(eval(ty2, ctx))
                    } else {
                        Err(format!("Illegal application param : {:?}", t2))
                    }
                }
                Ok(ty) => Err(format!("Illegal application to type: {:?}", ty)),
                Err(msg) => Err(format!("Illegal application: {:?}", msg)),
            }
        }
        InferTerm::Set => Ok(Type::VSet),
        InferTerm::Pi(l, r) => {
            if type_check(l.clone(), Type::VSet, context.clone(), index).is_ok() {
                let ty = eval(l, vec![]);
                context.insert(Local(index), ty);
                if type_check(subst(Free(Local(index)), r, 0), Type::VSet, context, index + 1).is_ok() {
                    return Ok(Type::VSet);
                }
            }
            Err("Unexpected pi values".to_string())
        }
        InferTerm::Ann(t, ty) => {
            if type_check(ty.clone(), Type::VSet, context.clone(), index).is_ok() {
                let ev_ty = eval(ty, vec![]);
                type_check(t, ev_ty.clone(), context, index);
                Ok(ev_ty)
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
                Type::VPi(l, r, mut ctx) => {
                    let typ = subst(InferTerm::Free(Name::Local(index)), *body, index);
                    context.insert(Local(index), *l);
                    ctx.push(Value::Neutral(Neutral::Free(Local(index))));
                    type_check(typ, eval(r, ctx), context, index + 1)
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
        InferTerm::Pi(l, r) => InferTerm::Pi(
            subst(s.clone(), l, index), subst(s, r, index + 1),
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

fn quote_neutral(neutral: Neutral, index: usize) -> InferTerm {
    match neutral {
        Neutral::Free(name) => InferTerm::Free(name),
        Neutral::App(l, r) => InferTerm::App(
            Box::new(quote_neutral(*l, index)), quote(*r, index),
        )
    }
}

fn quote(val: Value, index: usize) -> Term {
    match val {
        Value::Neutral(neutral) => {
            Term::Inf(Box::new(quote_neutral(neutral, index)))
        }
        Value::Lam(t, mut env) => {
            env.push(Value::Neutral(Neutral::Free(Name::Quote(index))));
            let v = eval(t, env);
            Term::Lam(Box::new(quote(v, index + 1)))
        }
        Value::VSet => Term::Inf(Box::new(InferTerm::Set)),
        Value::VPi(l, r, mut env) => {
            env.push(Value::Neutral(Neutral::Free(Name::Quote(index))));
            let v = eval(r, env);
            Term::Inf(Box::new(InferTerm::Pi(quote(*l, index), quote(v, index + 1))))
        }
    }
}

fn main() {

}

#[test]
fn ty_check_pass() {

}

#[test]
fn ty_check_fail() {

}
