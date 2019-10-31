#[derive(Clone, Eq, PartialEq, Debug)]
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

type BoundVar = Vec<Value>;

fn eval_infer(term: InferTerm, env: BoundVar) -> Value {
    match term {
        InferTerm::Free(name) => Value::Neutral(
            Neutral::Free(name)
        ),
        InferTerm::Bound(v) => {
            println!("bound vars {:?}", env);
            env[env.len() - v -1].clone()
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

fn main() {
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
                constv.clone(),
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
    println!("{:?}", eval_infer(expr2, vec![]));
}
