use super::signature::*;
use super::closure::*;
use super::hash::HashMap;
use std::fmt::{self, Display, Formatter};
use std::collections::VecDeque;
use std::iter::once;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Variable(String),
    Wildcard(Option<usize>),
    Operation(String, Vec<Term>),
}

impl Term {
    fn visit_subterms<'a, V: FnMut(&'a Term)>(&'a self, mut v: V) {
        self.visit_subterms_impl(&mut v);
    }
    fn visit_subterms_impl<'a, V: FnMut(&'a Term)>(&'a self, v: &mut V) {
        match self {
            Term::Operation(_, args) => {
                for arg in args {
                    arg.visit_subterms_impl(v);
                }
            },
            _ => (),
        }
        v(self);
    }

    fn assign_wildcard_indices(&mut self, mut next_index: usize) -> usize {
        match self {
            Term::Variable(_) => next_index,
            Term::Wildcard(None) => {
                *self = Term::Wildcard(Some(next_index));
                next_index + 1
            },
            Term::Wildcard(Some(_)) => panic!("Wildcard index already assigned"),
            Term::Operation(_, args) => {
                for arg in args {
                    next_index = arg.assign_wildcard_indices(next_index);
                }
                next_index
            }
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Term::Variable(var) => {
                f.write_str(var)
            },
            Term::Wildcard(index) => {
                f.write_str("_")?;
                if let Some(i) = index {
                    i.fmt(f)?;
                }
                Ok(())
            }
            Term::Operation(op, args) => {
                f.write_str(op)?;
                f.write_str("(")?;
                let mut arg_it = args.iter();
                if let Some(arg0) = arg_it.next() {
                    arg0.fmt(f)?;
                    
                    for arg in arg_it {
                        f.write_str(", ")?;
                        arg.fmt(f)?;
                    }
                }
                f.write_str(")")
            }
        }
    }
}

#[test]
fn test_term_display() {
    let v = Term::Variable("abc".to_string());
    assert_eq!(v.to_string(), "abc");
    let w = Term::Wildcard(None);
    assert_eq!(w.to_string(), "_");
    let o = Term::Operation("fun".to_string(), vec![v.clone(), w.clone()]);
    assert_eq!(o.to_string(), "fun(abc, _)");
    let o1 = Term::Operation("Fun".to_string(), vec![o.clone()]);
    assert_eq!(o1.to_string(), "Fun(fun(abc, _))");
    let o2 = Term::Operation("p".to_string(), vec![]);
    assert_eq!(o2.to_string(), "p()");
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Atom {
    Equal(Term, Term),
    Defined(Term),
    Predicate(String, Vec<Term>),
}

impl Atom {
    fn visit_subterms<'a, V: FnMut(&'a Term)>(&'a self, mut v: V) {
        match self {
            Atom::Equal(lhs, rhs) => {
                lhs.visit_subterms(&mut v);
                rhs.visit_subterms(&mut v);
            },
            Atom::Defined(t) => {
                t.visit_subterms(&mut v);
            },
            Atom::Predicate(_, args) => {
                for arg in args {
                    arg.visit_subterms(&mut v);
                }
            }
        }
    }
    fn assign_wildcard_indices(&mut self, mut next_index: usize) -> usize {
        match self {
            Atom::Equal(lhs, rhs) => {
                next_index = lhs.assign_wildcard_indices(next_index);
                rhs.assign_wildcard_indices(next_index)
            },
            Atom::Defined(t) => {
                t.assign_wildcard_indices(next_index)
            },
            Atom::Predicate(_, args) => {
                for arg in args {
                    next_index = arg.assign_wildcard_indices(next_index);
                }
                next_index
            }
        }
    }
}

impl Display for Atom {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Equal(lhs, rhs) => {
                lhs.fmt(f)?;
                f.write_str(" = ")?;
                rhs.fmt(f)
            },
            Atom::Defined(t) => {
                f.write_str("!")?;
                t.fmt(f)
            },
            Atom::Predicate(p, args) => {
                f.write_str(p)?;
                f.write_str("(")?;
                let mut arg_it = args.iter();
                if let Some(arg0) = arg_it.next() {
                    arg0.fmt(f)?;
                    
                    for arg in arg_it {
                        f.write_str(", ")?;
                        arg.fmt(f)?;
                    }
                }
                f.write_str(")")
            },
        }
    }
}

#[test]
fn test_atom_display() {
    let v = Term::Variable("abc".to_string());
    let w = Term::Wildcard(None);
    let o = Term::Operation("fun".to_string(), vec![v.clone(), w.clone()]);

    let e = Atom::Equal(v.clone(), w.clone());
    assert_eq!(e.to_string(), "abc = _");
    let d = Atom::Defined(o.clone());
    assert_eq!(d.to_string(), "!fun(abc, _)");
    let p = Atom::Predicate("p".to_string(), vec![v.clone(), o.clone()]);
    assert_eq!(p.to_string(), "p(abc, fun(abc, _))");
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Formula(pub Vec<Atom>);

impl Formula {
    fn visit_subterms<'a, V: FnMut(&'a Term)>(&'a self, mut v: V) {
        let Formula(atoms) = self;
        for atom in atoms {
            atom.visit_subterms(&mut v);
        }
    }
    fn assign_wildcard_indices(&mut self, mut next_index: usize) -> usize {
        for atom in &mut self.0 {
            next_index = atom.assign_wildcard_indices(next_index);
        }
        next_index
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let Formula(atoms) = self;
        let mut atom_it = atoms.iter();
        if let Some(atom0) = atom_it.next() {
            atom0.fmt(f)?;

            for atom in atom_it {
                f.write_str(" & ")?;
                atom.fmt(f)?;
            }
        }
        Ok(())
    }
}

#[test]
fn test_formula_display() {
    let abc = Term::Variable("abc".to_string());
    let xyz = Term::Variable("xyz".to_string());

    let e = Atom::Equal(abc.clone(), xyz.clone());
    let d = Atom::Defined(abc.clone());

    let f0 = Formula(vec![]);
    assert_eq!(f0.to_string(), "");
    let f1 = Formula(vec![e.clone()]);
    assert_eq!(f1.to_string(), "abc = xyz");
    let f2 = Formula(vec![e.clone(), d.clone()]);
    assert_eq!(f2.to_string(), "abc = xyz & !abc");
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sequent {
    Implication(Formula, Formula),
    Reduction(Term, Term),
    ConditionalReduction(Formula, Term, Term),
}

impl Sequent {
    fn visit_subterms<'a, V: FnMut(&'a Term)>(&'a self, mut v: V) {
        match self {
            Sequent::Implication(premise, conclusion) => {
                premise.visit_subterms(&mut v);
                conclusion.visit_subterms(&mut v);
            },
            Sequent::Reduction(from, to) => {
                from.visit_subterms(&mut v);
                to.visit_subterms(&mut v);
            },
            Sequent::ConditionalReduction(premise, from, to) => {
                premise.visit_subterms(&mut v);
                from.visit_subterms(&mut v);
                to.visit_subterms(&mut v);
            },
        }
    }
    pub fn assign_wildcard_indices(&mut self) -> usize {
        let mut next_index = 0;
        match self {
            Sequent::Implication(premise, conclusion) => {
                next_index = premise.assign_wildcard_indices(next_index);
                conclusion.assign_wildcard_indices(next_index)
            },
            Sequent::Reduction(from, to) => {
                next_index = from.assign_wildcard_indices(next_index);
                to.assign_wildcard_indices(next_index)
            },
            Sequent::ConditionalReduction(premise, from, to) => {
                next_index = premise.assign_wildcard_indices(next_index);
                next_index = from.assign_wildcard_indices(next_index);
                to.assign_wildcard_indices(next_index)
            },
        }
    }
}

impl Display for Sequent {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Sequent::Implication(premise, conclusion) => {
                premise.fmt(f)?;
                f.write_str(" => ")?;
                conclusion.fmt(f)
            },
            Sequent::Reduction(from, to) => {
                from.fmt(f)?;
                f.write_str(" ~> ")?;
                to.fmt(f)
            },
            Sequent::ConditionalReduction(premise, from, to) => {
                premise.fmt(f)?;
                f.write_str(" => ")?;
                from.fmt(f)?;
                f.write_str(" ~> ")?;
                to.fmt(f)
            },
        }
    }
}

#[macro_export]
macro_rules! term {
    ($x:ident) => {
        $crate::eqlog::syntax::Term::Variable(stringify!($x).to_string())
    };
    (_) => {
        $crate::eqlog::syntax::Term::Wildcard(None)
    };
    ($f:ident $arg:tt) => {
        term!(@impl
              (|args| $crate::eqlog::syntax::Term::Operation(stringify!($f).to_string(), args))
              []
              $arg
        )
    };

    // empty argument list
    (@impl $op:tt [] ()) => {
        $op(vec![])
    };

    // singleton argument list with variable
    (@impl $op:tt [] ($var:ident)) => {
        $op(vec![term!($var)])
    };
    // >= 2 arguments; last arg is variable
    (@impl $op:tt [$($parsed_arg:tt)*] ($var:ident) ) => {
        $op(vec![$($parsed_arg),* , (term!($var))])
    };
    // >= 2 arguments; head of unparsed args is variable
    (@impl $op:tt [$($parsed_arg:tt)*] ($var:ident, $($tail:tt)* )) => {
        term!(@impl $op [$($parsed_arg)* (term!($var))] ($($tail)*))
    };

    // singleton argument list with wildcard
    (@impl $op:tt [] (_)) => {
        $op(vec![term!(_)])
    };
    // >= 2 arguments; last arg is wildcard
    (@impl $op:tt [$($parsed_arg:tt)*] (_) ) => {
        $op(vec![$($parsed_arg),* , (term!(_))])
    };
    // >= 2 arguments; head of unparsed args is variable
    (@impl $op:tt [$($parsed_arg:tt)*] (_, $($tail:tt)* )) => {
        term!(@impl $op [$($parsed_arg)* (term!(_))] ($($tail)*))
    };

    // singleton argument list with function call
    (@impl $op:tt [] ($g:ident $arg:tt)) => {
        $op(vec![term!($g $arg)])
    };
    // >= 2 arguments; last arg is function call
    (@impl $op:tt [$($parsed_arg:tt)*] ($g:ident $arg:tt) ) => {
        $op(vec![$($parsed_arg),* , (term!($g $arg))])
    };
    // >= 2 arguments; head of unparsed args is function call
    (@impl $op:tt [$($parsed_arg:tt)*] ($g:ident $arg:tt, $($tail:tt)* )) => {
        term!(@impl $op [$($parsed_arg)* (term!($g $arg))] ($($tail)*))
        // $f($($parsed_arg),* term!($var))
    };
}

#[test]
fn test_term_macro() {
    assert_eq!(term!(_).to_string(), "_");
    assert_eq!(term!(asdf).to_string(), "asdf");
    assert_eq!(term!(f(asdf)).to_string(), "f(asdf)");
    assert_eq!(term!(f(x, asdf)).to_string(), "f(x, asdf)");
    assert_eq!(term!(f(g(x), asdf)).to_string(), "f(g(x), asdf)");
    assert_eq!(term!(f(g(), asdf)).to_string(), "f(g(), asdf)");
    assert_eq!(term!(f(g(), h())).to_string(), "f(g(), h())");
}

#[macro_export]
macro_rules! atom {
    // a defined term
    (! $($tm:tt)*) => {
        Atom::Defined(term!($($tm)*))
    };
    // a predicate applied to terms
    ($p:ident $args:tt) => {
        term!(@impl
              (|args| $crate::eqlog::syntax::Atom::Predicate(stringify!($p).to_string(), args))
              []
              $args
        )
    };
    // lhs is an operation term
    ($f:tt $args:tt = $($rhs:tt)*) => {
        Atom::Equal(term!($f $args), term!($($rhs)*))
    };
    // lhs is a variable
    ($lhs:tt = $($rhs:tt)*) => {
        Atom::Equal(term!($lhs), term!($($rhs)*))
    };
}

#[test]
fn test_atom_macro() {
    assert_eq!(atom!(x = y).to_string(), "x = y");
    assert_eq!(atom!(f(x) = y).to_string(), "f(x) = y");
    assert_eq!(atom!(x = g(y)).to_string(), "x = g(y)");
    assert_eq!(atom!(f(x, g(z)) = g(y)).to_string(), "f(x, g(z)) = g(y)");

    assert_eq!(atom!(!x).to_string(), "!x");
    assert_eq!(atom!(!f(x)).to_string(), "!f(x)");
    assert_eq!(atom!(!g(f(x), y)).to_string(), "!g(f(x), y)");

    assert_eq!(atom!(r()).to_string(), "r()");
    assert_eq!(atom!(r(x)).to_string(), "r(x)");
    assert_eq!(atom!(r(x, f(y))).to_string(), "r(x, f(y))");
    assert_eq!(atom!(r(g(x), y)).to_string(), "r(g(x), y)");
    assert_eq!(atom!(rel(g(x, y), y)).to_string(), "rel(g(x, y), y)");
}

#[macro_export]
macro_rules! formula {
    (@impl [$($atoms:tt)*] []) => {
        Formula(vec![$($atoms),*])
    };
    (@impl [$($prev_atoms:tt)*] [$($cur_atom:tt)*]) => {
        formula!(@impl [$($prev_atoms)* (atom!($($cur_atom)*))] [])
    };
    (@impl [$($prev_atoms:tt)*] [$($cur_atom:tt)*] & $($tail:tt)*) => {
        formula!(@impl [$($prev_atoms)* (atom!($($cur_atom)*))] [] $($tail)*)
    };
    (@impl $prev_atoms:tt [$($cur_atom:tt)*] $head:tt $($tail:tt)*) => {
        formula!(@impl $prev_atoms [$($cur_atom)* $head] $($tail)*)
    };

    ($($toks:tt)*) => {
        formula!(@impl [] [] $($toks)*)
    }
}

#[test]
fn test_formula_macro() {
    assert_eq!(formula!().to_string(), "");

    assert_eq!(formula!(f(x, g(z)) = g(y)).to_string(), "f(x, g(z)) = g(y)");
    assert_eq!(formula!(!g(f(x), y)).to_string(), "!g(f(x), y)");
    assert_eq!(formula!(rel(g(x, y), y)).to_string(), "rel(g(x, y), y)");

    assert_eq!(
        formula!(f(x, g(z)) = g(y) & !g(f(x), y)).to_string(),
        "f(x, g(z)) = g(y) & !g(f(x), y)"
    );
    assert_eq!(
        formula!(f(x, g(z)) = g(y) & !g(f(x), y) & rel(g(x, y), y)).to_string(),
        "f(x, g(z)) = g(y) & !g(f(x), y) & rel(g(x, y), y)"
    );
}

#[macro_export]
macro_rules! sequent {
    (@impl [$($from:tt)*] ~> $($to:tt)*) => {
        $crate::eqlog::syntax::Sequent::Reduction(
            term!($($from)*),
            term!($($to)*)
        )
    };
    (@impl [$($prem:tt)*] => $($con:tt)*) => {
        sequent!(@impl => [$($prem)*] [] $($con)*)
    };
    (@impl [$($from:tt)*] $to:tt $($tail:tt)*) => {
        sequent!(@impl [$($from)* $to] $($tail)*)
    };
    (@impl [$($from:tt)*]) => {
        compile_error!("Sequents must be of the form A => B, or a ~> b, or A => a ~> b")
    };
    (@impl => [$($prem:tt)*] [$($from:tt)*] ~> $($to:tt)*) => {
        $crate::eqlog::syntax::Sequent::ConditionalReduction(
            formula!($($prem)*),
            term!($($from)*),
            term!($($to)*),
        )
    };
    (@impl => [$($prem:tt)*] [$($con:tt)*]) => {
        $crate::eqlog::syntax::Sequent::Implication(
            formula!($($prem)*),
            formula!($($con)*)
        )
    };
    (@impl => [$($prem:tt)*] [$($con:tt)*] $head:tt $($tail:tt)*) => {
        sequent!(@impl => [$($prem)*] [$($con)* $head] $($tail)*)
    };
    ($($toks:tt)*) => {{
        let mut result = sequent!(@impl [] $($toks)*);
        result.assign_wildcard_indices();
        result
    }};
}


#[test]
fn test_sequent_macro() {
    //trace_macros!(true);
    //let _ = sequent!( r(x) => );
    //trace_macros!(false);
    assert_eq!(sequent!( => ).to_string(), " => ");
    assert_eq!(
        sequent!(f(x, g(z)) = g(y) => ).to_string(),
        "f(x, g(z)) = g(y) => "
    );
    assert_eq!(
        sequent!( => f(x, g(z)) = g(y)).to_string(),
        " => f(x, g(z)) = g(y)"
    );
    assert_eq!(
        sequent!(f(x, g(z)) = g(y) => r(g(x), y)).to_string(),
        "f(x, g(z)) = g(y) => r(g(x), y)"
    );
    assert_eq!(
        sequent!(f(x, g(z)) = g(y) & r(g(x), y) => a(x) & b()).to_string(),
        "f(x, g(z)) = g(y) & r(g(x), y) => a(x) & b()"
    );

    assert_eq!(
        sequent!(x ~> y).to_string(),
        "x ~> y"
    );
    assert_eq!(
        sequent!(f(x, g(z)) ~> g(y)).to_string(),
        "f(x, g(z)) ~> g(y)"
    );
    assert_eq!(
        sequent!(!f(_) & r(g(x), _) & x = _ => r(_, _)).to_string(),
        "!f(_0) & r(g(x), _1) & x = _2 => r(_3, _4)"
    );
    assert_eq!(
        sequent!(x = y & r(x, z) => f(x) ~> g(y, z)).to_string(),
        "x = y & r(x, z) => f(x) ~> g(y, z)"
    );
    assert_eq!(
        sequent!( => f(x) ~> g(y, z)).to_string(),
        " => f(x) ~> g(y, z)"
    );
}


fn check_occurence(seq: &Sequent) {
    let mut var_occurences: HashMap<&str, usize> = HashMap::default();
    seq.visit_subterms(|t| {
        match t {
            Term::Variable(name) => {
                match var_occurences.get_mut(name.as_str()) {
                    Some(occ) => *occ += 1,
                    None => {
                        var_occurences.insert(name, 1);
                    },
                }
            },
            _ => (),
        }
    });

    for (name, occ_num) in var_occurences {
        if occ_num == 1 {
            panic!("Variable {} used only once", name);
        }
    }
}

fn to_presentation<'a, Sig: Signature>(
    signature: Sig,
    formula: &'a Formula,
) -> (Presentation<Sig::Relation>, HashMap<&'a Term, (usize, Sig::Sort)>) 
where
    Sig::Sort: Display,
    Sig::Relation: Display,
    Sig::Relation: PredicateOrOperation,
{
    let predicates: HashMap<String, Sig::Relation> =
        signature.relations().iter().cloned().
        filter(|r| r.kind() == RelationKind::Predicate).
        map(|r| (r.to_string(), r)).
        collect();
    let operations: HashMap<String, Sig::Relation> =
        signature.relations().iter().cloned().
        filter(|r| r.kind() == RelationKind::Operation).
        map(|r| (r.to_string(), r)).
        collect();

    let mut added_terms: HashMap<&'a Term, (usize, Sig::Sort)> = HashMap::default();
    let mut presentation = Presentation { relations: vec![], equalities: vec![] };
    let mut row_len: usize = 0;

    let mut term_queue: VecDeque<&Term> = VecDeque::new();
    for atom in &formula.0 {
        match atom {
            Atom::Equal(lhs, rhs) => {
                term_queue.push_back(lhs);
                term_queue.push_back(rhs);
            },
            Atom::Defined(t) => {
                term_queue.push_back(t);
            },
            Atom::Predicate(name, args) => {
                let &r = predicates.get(name).unwrap_or_else(|| panic!(
                    "{}: Undeclared predicate symbol",
                    name,
                ));
                presentation.relations.push(r);

                let arity = signature.arity(r);
                assert!(
                    args.len() == arity.len(),
                    "{}: Predicate {} takes {} arguments but is applied to {} arguments",
                    atom, name, arity.len(), args.len(),
                );

                for (local_index, (arg, sort)) in args.iter().zip(arity).enumerate() {
                    let global_index = row_len + local_index;
                    if let Some((global_index0, sort0)) = added_terms.get(arg) {
                        assert!(
                            *sort0 == *sort,
                            "Sort mismatch: {} must have sort {} but has sort {}",
                            arg, sort, sort0,
                        );
                        presentation.equalities.push((*global_index0, global_index));
                    } else {
                        added_terms.insert(arg, (global_index, *sort));
                        term_queue.push_back(arg);
                    }
                }
                row_len += args.len();
            },
        }
    }

    while let Some(t) = term_queue.pop_front() {
        if let Term::Operation(name, args) = t  {
            let &r = operations.get(name).unwrap_or_else(|| panic!(
                "{}: Undeclared operation symbol",
                name,
            ));
            presentation.relations.push(r);

            let arity = signature.arity(r);
            assert!(
                args.len() == arity.len() - 1,
                "{}: Operation {} takes {} arguments but is applied to {} arguments",
                t, name, arity.len() - 1, args.len(),
            );

            for (local_index, (arg, sort)) in args.iter().chain(once(t)).zip(arity).enumerate() {
                let global_index = row_len + local_index;
                if let Some((global_index0, sort0)) = added_terms.get(arg) {
                    assert!(
                        *sort0 == *sort,
                        "Sort mismatch: {} must have sort {} but has sort {}",
                        arg, sort, sort0,
                    );
                    presentation.equalities.push((*global_index0, global_index));
                } else {
                    added_terms.insert(arg, (global_index, *sort));
                }
            }
            for arg in args {
                term_queue.push_back(arg);
            }
            row_len += args.len() + 1;
        }
    }

    for atom in &formula.0 {
        match atom {
            Atom::Predicate(_, _) => {},
            Atom::Defined(t) => {
                assert!(
                    added_terms.contains_key(t),
                    "Variable or wildcard {} must be defined in premise but is never used",
                    t
                );
            },
            Atom::Equal(lhs, rhs) => {
                let lhs_index = added_terms.get(lhs).cloned();
                let rhs_index = added_terms.get(rhs).cloned();
                match (lhs_index, rhs_index) {
                    (Some((i, s)), Some((j, t))) => {
                        assert!(
                            s == t,
                            "Sort mismatch: {} has sort {} but {} has sort {}",
                            lhs, s, rhs, t,
                        );
                        presentation.equalities.push((i, j)); },
                    (Some((i, s)), _) => { added_terms.insert(rhs, (i, s)); },
                    (_, Some((j, t))) => { added_terms.insert(lhs, (j, t)); },
                    _ => panic!("Neither {} nor {} appear in operation or predicate", lhs, rhs),
                }
            }
        }
    }

    (presentation, added_terms)
}

pub fn to_surjection_presentation_impl<'a, Sig: Signature>(
    signature: Sig,
    premise: &'a Formula,
    conclusion: &'a Formula,
) -> SurjectionPresentation<Sig::Relation>
where
    Sig::Sort: Display,
    Sig::Relation: Display,
    Sig::Relation: PredicateOrOperation,
{
    let (domain, mut added_terms) = to_presentation(&signature, premise);

    let predicates: HashMap<String, Sig::Relation> =
        signature.relations().iter().cloned().
        filter(|r| r.kind() == RelationKind::Predicate).
        map(|r| (r.to_string(), r)).
        collect();
    let operations: HashMap<String, Sig::Relation> =
        signature.relations().iter().cloned().
        filter(|r| r.kind() == RelationKind::Operation).
        map(|r| (r.to_string(), r)).
        collect();

    let mut codomain_equalities: Vec<(usize, usize)> = vec![];
    let mut codomain_relations: Vec<(Sig::Relation, Vec<usize>)> = vec![];

    for atom in &conclusion.0 {
        match atom {
            Atom::Predicate(name, args) => {
                let &r = predicates.get(name).unwrap();

                let arity = signature.arity(r);
                assert!(
                    args.len() == arity.len(),
                    "{}: Predicate {} takes {} arguments but is applied to {} arguments",
                    atom, name, arity.len(), args.len(),
                );

                let indices =
                    args.iter().
                    zip(arity).
                    map(|(arg, sort)| {
                        let (index, sort0) = added_terms.get(arg).unwrap_or_else(|| {
                            panic!("{} is not defined in conclusion", arg);
                        });
                        assert!(
                            *sort0 == *sort,
                            "Sort mismatch: {} must have sort {} but has sort {}",
                            arg, sort, sort0,
                        );
                        *index
                    }).
                    collect();
                codomain_relations.push((r, indices));
            },
            Atom::Equal(lhs, rhs) => {
                let mut define_term_as = |
                    term: &'a Term,
                    result: usize,
                    added_terms: &mut HashMap<&'a Term, (usize, Sig::Sort)>,
                | -> Sig::Sort {
                    if let Term::Operation(name, args) = term {
                        let &r = operations.get(name).unwrap_or_else(|| panic!(
                            "{}: Undeclared operation symbol",
                            name
                        ));

                        let arity = signature.arity(r);
                        assert!(
                            args.len() == arity.len() - 1,
                            "{}: Operation {} takes {} arguments but is applied to {} arguments",
                            term, name, arity.len() - 1, args.len(),
                        );

                        let indices =
                            args.iter().
                            zip(arity).
                            map(|(arg, sort)| {
                                let (index, sort0) = added_terms.get(arg).unwrap_or_else(|| {
                                    panic!("{} is not defined in conclusion", arg);
                                });
                                assert!(
                                    *sort0 == *sort,
                                    "Sort mismatch: {} must have sort {} but has sort {}",
                                    arg, *sort, *sort0,
                                );
                                *index
                            }).
                            chain(once(result)).
                            collect();
                        codomain_relations.push((r, indices));

                        let s = *arity.last().unwrap();
                        added_terms.insert(term, (result, s));
                        s
                    } else {
                        panic!("Cannot make wildcard or variable {} defined in conclusion", term)
                    }
                };

                let lhs_index = added_terms.get(lhs).cloned();
                let rhs_index = added_terms.get(rhs).cloned();
                let (s, t) = match (lhs_index, rhs_index) {
                    (Some((i, s)), Some((j, t))) => {
                        codomain_equalities.push((i, j));
                        (s, t)
                    },
                    (Some((i, s)), None) => {
                        let t = define_term_as(rhs, i, &mut added_terms);
                        (s, t)
                    },
                    (None, Some((j, t))) => {
                        let s = define_term_as(lhs, j, &mut added_terms);
                        (s, t)
                    },
                    (None, None) => {
                        panic!("Both {} and {} are not defined in conclusion", lhs, rhs);
                    },
                };
                assert!(
                    s == t,
                    "Sort mismatch: {} has sort {} but {} has sort {}",
                    lhs, s, rhs, t,
                );
            },
            Atom::Defined(_) => panic!("Cannot use \"!\" to make term defined in conclusion"),
        }
    }

    SurjectionPresentation {
        domain,
        codomain_equalities,
        codomain_relations,
    }
}

pub fn to_surjection_presentation<Sig: Signature>(
    signature: Sig,
    sequent: &Sequent,
) -> SurjectionPresentation<Sig::Relation>
where
    Sig::Sort: Display,
    Sig::Relation: Display,
    Sig::Relation: PredicateOrOperation,
{
    check_occurence(sequent);

    match sequent {
        Sequent::Implication(premise, conclusion) => {
            to_surjection_presentation_impl(signature, premise, conclusion)
        },
        Sequent::Reduction(from, to) => {
            to_surjection_presentation(
                signature,
                &Sequent::ConditionalReduction(Formula(vec![]), from.clone(), to.clone())
            )
        },
        Sequent::ConditionalReduction(prem, from, to) => {
            let mut premise = prem.0.clone(); 
            premise.push(Atom::Defined(to.clone()));
            if let Term::Operation(_, args) = &from {
                premise.extend(
                    args.iter().
                    cloned().
                    map(Atom::Defined)
                );
            }
            let conclusion = vec![Atom::Equal(from.clone(), to.clone())];
            to_surjection_presentation_impl(
                signature,
                &Formula(premise),
                &Formula(conclusion),
            )
        },
    }
}

#[cfg(test)]
mod test_presentations {
    use super::*;

    arities!{
        pub enum Sort {S0, S1},
        pub enum Relation {
            O: S1 x S0 -> S1,
            P: S0 x S1,
            Q: S0 x S0,
            R: S1 x S1,
            Plus: S1 x S1 -> S1,
        },
    }
    use Relation::*;
    fn sig() -> StaticSignature<Sort, Relation> {
        StaticSignature::new()
    }

    #[test]
    fn trivial_sequent() {
        let sp = to_surjection_presentation(sig(), &sequent!(
             => 
        ));
        let _ = sp.clone().checked(sig());
        assert_eq!(sp.domain.relations, vec![]);
        assert_eq!(sp.domain.equalities, vec![]);
        assert_eq!(sp.codomain_relations, vec![]);
        assert_eq!(sp.codomain_equalities, vec![]);
    }

    #[test]
    fn equality_in_premise() {
        let sp0 = to_surjection_presentation(sig(), &sequent!(
            Q(x, y) & x = y => 
        ));
        let _ = sp0.clone().checked(sig());
        assert_eq!(sp0, to_surjection_presentation(sig(), &sequent!(
            Q(x, x) =>
        )));

        assert_eq!(sp0.domain.relations, vec![Q]);
        assert_eq!(sp0.domain.equalities, vec![(0, 1)]);
        assert_eq!(sp0.codomain_relations, vec![]);
        assert_eq!(sp0.codomain_equalities, vec![]);

        let sp1 = to_surjection_presentation(sig(), &sequent!(
            P(x, O(_, x)) & P(x0, O(_, x0)) & x = x0 => 
        ));
        let _ = sp1.clone().checked(sig());
        // P(0, 1) & P(2, 3) & o(4, 5, 6) & O(7, 8, 9) & <equalities> => 

        assert_eq!(sp1.domain.relations, vec![P, P, O, O]);
        assert_eq!(
            sp1.domain.equalities.clone().sort(),
            vec![(1, 6), (0, 5), (3, 9), (2, 8), (0, 2)].sort()
        );
        assert_eq!(sp1.codomain_relations, vec![]);
        assert_eq!(sp1.codomain_equalities, vec![]);
    }

    #[test]
    fn equality_in_conclusion() {
        let sp0 = to_surjection_presentation(sig(), &sequent!(
            Q(x, y) & Q(y, x) => x = y
        ));
        let _ = sp0.clone().checked(sig());
        assert_eq!(sp0.domain.relations, vec![Q, Q]);
        assert_eq!(sp0.domain.equalities.clone().sort(), vec![(0, 3), (1, 2)].sort());
        assert_eq!(sp0.codomain_relations, vec![]);
        assert_eq!(sp0.codomain_equalities, vec![(0, 1)]);

        let sp1 = to_surjection_presentation(sig(), &sequent!(
            !O(x, y) & !O(x, y0) => O(x, y) = O(x, y0)
        ));
        let _ = sp1.clone().checked(sig());
        assert_eq!(sp1.domain.relations, vec![O, O]);
        assert_eq!(sp1.domain.equalities, vec![(0, 3)]);
        assert_eq!(sp1.codomain_relations, vec![]);
        assert_eq!(sp1.codomain_equalities, vec![(2, 5)]);
    }

    #[test]
    fn predicate_in_conclusion() {
        let sp = to_surjection_presentation(sig(), &sequent!(
            Q(x, y) => Q(y, x)
        ));
        let _ = sp.clone().checked(sig());
        assert_eq!(sp.domain.relations, vec![Q]);
        assert_eq!(sp.domain.equalities, vec![]);
        assert_eq!(sp.codomain_relations, vec![(Q, vec![1, 0])]);
        assert_eq!(sp.codomain_equalities, vec![]);
    }

    #[test]
    fn operation_in_conclusion() {
        let sp = to_surjection_presentation(sig(), &sequent!(
            !O(x, y) & P(y, x0) => O(x, y) = O(x0, y)
        ));
        let _ = sp.clone().checked(sig());
        assert_eq!(sp.domain.relations, vec![P, O]);
        assert_eq!(sp.domain.equalities, vec![(0, 3)]);
        assert_eq!(sp.codomain_relations, vec![(O, vec![1, 0, 4])]);
        assert_eq!(sp.codomain_equalities, vec![]);
    }

    #[test]
    fn reduction() {
        let sp0 = to_surjection_presentation(sig(), &sequent!(
            O(O(x, y), y) ~> O(x, y)
        ));
        let _ = sp0.clone().checked(sig());
        assert_eq!(sp0.domain.relations, vec![O, O]);
        assert_eq!(sp0.domain.equalities.clone().sort(), vec![(0, 3), (1, 4)].sort());
        assert_eq!(sp0.codomain_relations, vec![(O, vec![2, 1, 2])]);
        assert_eq!(sp0.codomain_equalities, vec![]);

        let sp1 = to_surjection_presentation(sig(), &sequent!(
            Plus(X, Y) ~> Plus(Y, X)
        ));
        let _ = sp1.clone().checked(sig());
        assert_eq!(sp1.domain.relations, vec![Plus]);
        assert_eq!(sp1.domain.equalities, vec![]);
        assert_eq!(sp1.codomain_relations, vec![(Plus, vec![1, 0, 2])]);
        assert_eq!(sp1.codomain_equalities, vec![]);

        let sp2 = to_surjection_presentation(sig(), &sequent!(
            Plus(X, Plus(X, Plus(X, X))) ~> X
        ));
        let _ = sp2.clone().checked(sig());
        assert_eq!(sp2.domain.relations, vec![Plus, Plus]);
        assert_eq!(
            sp2.domain.equalities.clone().sort(),
            vec![(0, 3), (0, 4), (1, 5)].sort()
        );
        assert_eq!(sp2.codomain_relations, vec![(Plus, vec![0, 2, 0])]);
        assert_eq!(sp2.codomain_equalities, vec![]);
    }

    #[test]
    fn conditional_reduction() {
        let sp1 = to_surjection_presentation(sig(), &sequent!(
            R(X, Y) => Plus(X, Y) ~> Plus(Y, X)
        ));
        let _ = sp1.clone().checked(sig());
        assert_eq!(sp1.domain.relations, vec![R, Plus]);
        assert_eq!(
            sp1.domain.equalities.clone().sort(),
            vec![(0, 3), (1, 2)].clone().sort()
        );
        assert_eq!(sp1.codomain_relations, vec![(Plus, vec![0, 1, 4])]);
        assert_eq!(sp1.codomain_equalities, vec![]);
    }

    #[test] #[should_panic]
    fn variable_used_once() {
        to_surjection_presentation(sig(), &sequent!(
            Q(x, y) & => Q(x, x)
        ));
    }

    #[test] #[should_panic]
    fn not_surjective_variable() {
        to_surjection_presentation(sig(), &sequent!(
            Q(x, _) => Q(x, z) & Q(x, z)
        ));
    }

    #[test] #[should_panic]
    fn not_surjective_operation() {
        to_surjection_presentation(sig(), &sequent!(
            P(x, y) & P(x, z) => O(y, x) = O(z, x)
        ));
    }

    #[test] #[should_panic]
    fn predicate_arity_number() {
        to_surjection_presentation(sig(), &sequent!(
            Q(x, y, z) & Q(y, x, z) =>
        ));
    }

    #[test] #[should_panic]
    fn predicate_arity_sorts() {
        to_surjection_presentation(sig(), &sequent!(
            P(x, y) & P(O(y, x), y) =>
        ));
    }

    #[test] #[should_panic]
    fn operation_arity_number() {
        to_surjection_presentation(sig(), &sequent!(
            !O(y, _, x) => P(x, y)
        ));
    }

    #[test] #[should_panic]
    fn operation_arity_sorts() {
        to_surjection_presentation(sig(), &sequent!(
            !O(y, x) => O(x, y) = O(y, x)
        ));
    }

    #[test] #[should_panic]
    fn defined_variable() {
        to_surjection_presentation(sig(), &sequent!(
            P(x, _) & !z & => P(x, z)
        ));
    }

    #[test] #[should_panic]
    fn defined_in_conclusion() {
        to_surjection_presentation(sig(), &sequent!(
            P(x, y) => !O(y, x)
        ));
    }
}
