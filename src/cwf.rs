use crate::eqlog::signature::*;
use crate::eqlog::syntax::*;
use crate::eqlog::closure::*;
use crate::eqlog::model::*;
use crate::eqlog::element::*;
use std::iter::once;
use std::collections::{HashSet, HashMap};
use std::convert::TryFrom;

arities!{
    pub enum CwfSort {Ctx, Mor, Ty, Tm},
    pub enum CwfRelation {
        Dom: Mor -> Ctx,
        Cod: Mor -> Ctx,
        Comp: Mor x Mor -> Mor,
        Id: Ctx -> Mor,

        TyCtx: Ty -> Ctx,
        TmTy: Tm -> Ty,
        SubstTy: Mor x Ty-> Ty,
        SubstTm: Mor x Tm-> Tm,

        ExtCtx: Ctx x Ctx,
        // ExtCtx(G, D) should hold if a D is a (single step) extension of G
        // The variable, its type and weaking can be retrieved with the following:
        ExtTy: Ctx -> Ty,
        // ExtTy(D) must be defined if and only if Ext(G, D)
        Wkn: Ctx -> Mor,
        // Wkn(D) should only be defined if D = G.sigma for (unique) G and sigma
        Var: Ctx -> Tm,
        // Var(D) should only be defined if D = G.sigma for (unique) G and sigma
        MorExt: Ctx x Mor x Tm -> Mor,
        // MorExt(D, f, s) should only be defined if D = Dom(f).sigma for some sigma
        
        IterExtCtx: Ctx x Ctx, // the transitive closure of ExtCtx
        
        Unit: Ctx -> Ty,
        UnitTm: Ctx -> Tm,

        Bool: Ctx -> Ty,
        True: Ctx -> Tm,
        False: Ctx -> Tm,
        Neg: Tm -> Tm,
        BoolElim: Ty x Tm x Tm -> Tm, // BoolElim(sigma, true_case, false_case)
        // If BoolElim(sigma, true_case, false_case), then we should have TmTy(sigma) = G.Bool(G)
        // for some G and true_case: <id, true>(sigma), false_case: <id, false>(sigma)

        Eq: Tm x Tm -> Ty,
        Refl: Tm -> Tm,
    },
}
pub type CwfSignature = StaticSignature<CwfSort, CwfRelation>;

pub type Cwf = Model<CwfSignature>;

lazy_static! { static ref CWF_AXIOMS: Vec<CheckedSurjectionPresentation<CwfSignature>> =
    vec![
        // domain and codomain of identities
        sequent!(Dom(Id(x)) ~> x),
        sequent!(Cod(Id(x)) ~> x),

        // domain and codomain of composition
        sequent!(Dom(Comp(_, f)) ~> Dom(f)),
        sequent!(Cod(Comp(g, _)) ~> Cod(g)),

        // identity is a left and right identity
        sequent!(Comp(f, Id(Dom(f))) ~> f),
        sequent!(Comp(Id(Cod(f)), f) ~> f),

        // composition is associative
        // TODO: are both direction needed?
        sequent!(Comp(h, Comp(g, f)) ~> Comp(Comp(h, g), f)),
        sequent!(Comp(Comp(h, g), f) ~> Comp(h, Comp(g, f))),


        // context and type of substitutions
        sequent!(TyCtx(SubstTy(f, _)) ~> Cod(f)),
        sequent!(TmTy(SubstTm(f, s)) ~> SubstTy(f, TmTy(s))),

        // functoriality of substitution: identity
        sequent!(SubstTy(Id(TyCtx(sigma)), sigma) ~> sigma),
        sequent!(SubstTm(Id(TyCtx(TmTy(s))), s) ~> s),

        // functoriality of substitution: composition
        // TODO: are both direction needed?
        sequent!(SubstTy(g, SubstTy(f, sigma)) ~> SubstTy(Comp(g, f), sigma)),
        sequent!(SubstTy(Comp(g, f), sigma) ~> SubstTy(g, SubstTy(f, sigma))),
        sequent!(SubstTm(g, SubstTm(f, s)) ~> SubstTm(Comp(g, f), s)),
        sequent!(SubstTm(Comp(g, f), s) ~> SubstTm(g, SubstTm(f, s))),


        // domain and codomain of the weakening map
        sequent!(Cod(Wkn(Gsigma)) ~> Gsigma),
        sequent!(ExtCtx(G, Gsigma) => Dom(Wkn(Gsigma)) ~> G),

        // type of the variable
        sequent!(TmTy(Var(Gsigma)) ~> SubstTy(Wkn(Gsigma), ExtTy(Gsigma))),

        // domain and codomain of extended morphisms
        sequent!(Cod(MorExt(_, f, _)) ~> Cod(f)),
        sequent!(Dom(MorExt(Gsigma, _, _)) ~> Gsigma),
        
        // base & variable compatibility of extended morphisms
        sequent!(Comp(MorExt(Gsigma, f, _), Wkn(Gsigma)) ~> f),
        sequent!(SubstTm(MorExt(Gsigma, _, s), Var(Gsigma)) ~> s),

        // uniqueness of extended morphisms
        sequent!(
            Comp(g, Wkn(Gsigma)) = f & SubstTm(g, Var(Gsigma)) = s
            =>
            g = MorExt(Gsigma, f, s)
        ),

        sequent!(ExtCtx(G, Gsigma) => IterExtCtx(G, Gsigma)),
        sequent!(IterExtCtx(G, D) & IterExtCtx(D, E) => IterExtCtx(G, E)),

        // context and types of unit constants
        sequent!(TyCtx(Unit(G)) ~> G),
        sequent!(TmTy(UnitTm(G)) ~> Unit(G)),

        // substitution stability of unit constants
        sequent!(SubstTy(f, Unit(Dom(f))) ~> Unit(Cod(f))),
        sequent!(SubstTm(f, UnitTm(Dom(f))) ~> UnitTm(Cod(f))),

        // uniquness of UniqueEl
        sequent!(TmTy(t) = Unit(G) => t = UnitTm(G)),

        // context and types of bool constants
        sequent!(TyCtx(Bool(G)) ~> G),
        sequent!(TmTy(True(G)) ~> Bool(G)),
        sequent!(TmTy(False(G)) ~> Bool(G)),
        sequent!(TmTy(Neg(b)) ~> TmTy(b)),

        // substitution stability of bool constants
        sequent!(SubstTy(f, Bool(Dom(f))) ~> Bool(Cod(f))),
        sequent!(SubstTm(f, True(Dom(f))) ~> True(Cod(f))),
        sequent!(SubstTm(f, False(Dom(f))) ~> False(Cod(f))),
        sequent!(SubstTm(f, Neg(b)) ~> Neg(SubstTm(f, b))),

        // computation rules for negation
        sequent!(Neg(True(G)) ~> False(G)),
        sequent!(Neg(False(G)) ~> True(G)),

        // type of bool elimination
        sequent!(TmTy(BoolElim(sigma, _, _)) ~> sigma),
        // substituting true and false into bool elimination
        sequent!(
            TyCtx(sigma) = Gbool
            =>
            SubstTm(MorExt(Gbool, f, True(Cod(f))), BoolElim(sigma, true_case, _)) ~> true_case
        ),
        sequent!(
            TyCtx(sigma) = Gbool
            =>
            SubstTm(MorExt(Gbool, f, False(Cod(f))), BoolElim(sigma, _, false_case)) ~> false_case
        ),
        // Uniqueness of bool elimination
        sequent!(
            ExtCtx(G, Gbool) & ExtTy(Gbool) = Bool(G) & TyCtx(sigma) = Gbool & TmTy(s) = sigma &
            SubstTm(MorExt(Gbool, id, True(G)), s) = s_true &
            SubstTm(MorExt(Gbool, id, False(G)), s) = s_false
            =>
            s = BoolElim(sigma, s_true, s_false)
        ),
        // TODO: is substitution stability of bool elimination necessary or will this follow from
        // uniqueness?

        // context of equality types
        sequent!(TyCtx(Eq(s, _)) ~> TyCtx(TmTy(s))),
        // substitution stability of equality types
        sequent!(SubstTy(f, Eq(s, t)) ~> Eq(SubstTm(f, s), SubstTm(f, t))),

        // type of refl
        sequent!(TmTy(Refl(s)) ~> Eq(s, s)),
        // substitution stability of refl (the equality follows from equality reflection)
        sequent!(SubstTm(f, Refl(s)) ~> Refl(SubstTm(f, s))),
        // equality reflection
        sequent!(eq_ty = Eq(s, t) & TmTy(e0) = eq_ty & TmTy(e1) = eq_ty => s = t & e0 = e1),
    ].iter().
    map(|s| to_surjection_presentation(CwfSignature::new(), s).checked(CwfSignature::new())).
    chain(
        CwfSignature::new().relations().iter().
        filter(|r| r.kind() == RelationKind::Operation).
        map(|r| CheckedSurjectionPresentation::functionality(CwfSignature::new(), *r))
    ).
    collect();
}

#[test]
fn test_cwf_axioms() {
    let _ = *CWF_AXIOMS;
}

fn rows_with_result(cwf: &Cwf, el: Element) -> Vec<(CwfRelation, Vec<Element>)> {
    let mut result = Vec::new(); 
    let sig = CwfSignature::new();
    let el_sort = cwf.element_sort(el);

    for &rel_sym in sig.relations() {
        if *sig.arity(rel_sym).last().unwrap() != el_sort {
            continue;
        }

        for row in cwf.rows(rel_sym) {
            if *row.last().unwrap() == el {
                let mut args = row.to_vec();
                args.pop();
                result.push((rel_sym, args));
            }
        }
    }

    result
}

fn format_operation(rel_sym: CwfRelation, args: &[&str]) -> String {
    if rel_sym == CwfRelation::ExtCtx {
        return format!("{}.?", args[0]);
    }

    if rel_sym == CwfRelation::Comp {
        return format!("{} o {}", args[0], args[1]);
    }

    if rel_sym == CwfRelation::Wkn {
        return format!("p_{}", args[0]);
    }

    if rel_sym == CwfRelation::Id {
        return format!("id_{}", args[0]);
    }

    if rel_sym == CwfRelation::MorExt {
        return format!("<{}, {}>_{}", args[1], args[2], args[0]);
    }

    let mut result = String::new();
    result.push_str(&format!("{:?}", rel_sym));
    result.push_str("(");
    if args.is_empty() {
        result.push_str(")");
        return result;
    }

    result.push_str(*args.first().unwrap());
    for arg in &args[1 ..] {
        result.push_str(", ");
        result.push_str(*arg);
    }
    result.push_str(")");
    result
}

fn assign_names(cwf: &Cwf) -> HashMap<Element, String> {
    let mut result = HashMap::new();

    result.extend(
        cwf.sort_elements(CwfSort::Ctx)
        .zip((0 ..).map(|i| format!("G{}", i)))
    );

    result.extend(
        cwf.sort_elements(CwfSort::Mor)
        .zip((0 ..).map(|i| format!("f{}", i)))
    );

    result
}

fn format_cwf(cwf: &Cwf) -> String {
    let mut result = String::new();

    let names = assign_names(cwf);

    for ctx in cwf.sort_elements(CwfSort::Ctx) {
        if ctx != cwf.representative_const(ctx) {
            continue;
        }

        result.push_str(&format!("Ctx {}", names.get(&ctx).unwrap()));
        let equal_ctxs =
            cwf.sort_elements(CwfSort::Ctx)
            .filter(|&other_ctx| other_ctx != ctx && cwf.representative_const(other_ctx) == ctx);
        for equal_ctx in equal_ctxs {
            result.push_str(&format!(" = {}", names.get(&equal_ctx).unwrap()));
        }
        result.push_str(":\n");

        for (rel_sym, args) in rows_with_result(cwf, ctx) {
            if rel_sym == CwfRelation::Dom || rel_sym == CwfRelation::Cod || rel_sym == CwfRelation::TyCtx {
                continue;
            }
            let arg_names: Vec<&str> =
                args.into_iter()
                .map(|arg| names.get(&arg).map(|s| s.as_str()).unwrap_or("?"))
                .collect();
            result.push_str(&format!("\t= {}\n", format_operation(rel_sym, &arg_names)));
        }
    }


    for mor in cwf.sort_elements(CwfSort::Mor) {
        if mor != cwf.representative_const(mor) {
            continue;
        }

        result.push_str(&format!("Mor {}", names.get(&mor).unwrap()));
        let equal_mors =
            cwf.sort_elements(CwfSort::Mor)
            .filter(|&other_mor| other_mor != mor && cwf.representative_const(other_mor) == mor);
        for equal_mor in equal_mors {
            result.push_str(&format!(" = {}", names.get(&equal_mor).unwrap()));
        }

        let dom = cwf.rows(CwfRelation::Dom).find(|row| row[0] == mor).map(|row| row[1]).unwrap();
        let cod = cwf.rows(CwfRelation::Cod).find(|row| row[0] == mor).map(|row| row[1]).unwrap();

        result.push_str(&format!(" : {} -> {}\n", names.get(&dom).unwrap(), names.get(&cod).unwrap()));
        for (rel_sym, args) in rows_with_result(cwf, mor) {
            if rel_sym == CwfRelation::Dom || rel_sym == CwfRelation::Cod || rel_sym == CwfRelation::TyCtx {
                continue;
            }
            let arg_names: Vec<&str> =
                args.into_iter()
                .map(|arg| names.get(&arg).map(|s| s.as_str()).unwrap_or("?"))
                .collect();
            result.push_str(&format!("\t= {}\n", format_operation(rel_sym, &arg_names)));
        }
    }

    result
}

pub fn close_cwf(cwf: &mut Cwf) {
    close_model(CWF_AXIOMS.as_slice(), cwf);
}

pub fn els_are_equal(cwf: &mut Cwf, lhs: Element, rhs: Element) -> bool {
    assert_eq!(cwf.element_sort(lhs), cwf.element_sort(rhs));
    cwf.representative(lhs) == cwf.representative(rhs)
}

pub fn adjoin_op(cwf: &mut Cwf, op: CwfRelation, args: Vec<Element>) -> Element {
    assert_eq!(op.kind(), RelationKind::Operation);

    let before = cwf.clone();

    let dom_len: usize = op.arity().len() - 1;
    let op_dom: &[CwfSort] = &op.arity()[.. dom_len];
    let cod: CwfSort = *op.arity().last().unwrap();

    assert!(op_dom.iter().cloned().eq(args.iter().map(|arg| cwf.element_sort(*arg))));

    let result = cwf.adjoin_element(cod);
    let mut row = args;
    row.push(result);
    cwf.adjoin_rows(op, once(row));

    close_cwf(cwf);

    for ctx in cwf.sort_elements(CwfSort::Ctx) {
        if ctx != cwf.representative_const(ctx) {
            println!("Before:");
            println!("{}", format_cwf(&before));
            println!("Now:");
            println!("{}", format_cwf(cwf));
            panic!("Contexts equated")
        }
    }

    result
}

pub fn tm_ty(cwf: &mut Cwf, tm: Element) -> Element {
    adjoin_op(cwf, CwfRelation::TmTy, vec![tm])
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct MorphismWithSignature {
    pub morph: Element,
    pub dom: Element,
    pub cod: Element,
}

fn adjoin_post_compositions_step(
    cwf: &mut Cwf,
    dom_root_ctx: Element,
    after_morphisms: impl IntoIterator<Item = MorphismWithSignature>,
) -> Vec<MorphismWithSignature> {

    let before_morphisms: Vec<MorphismWithSignature> =
        cwf.rows(CwfRelation::Dom)
        .filter_map(|dom_row| {
            let [morph, dom] = <[Element; 2]>::try_from(dom_row).unwrap();

            // TODO: checking `dom != dom_root_ctx` shouldn't be neccessary once IterExtCtx can be
            // made reflexive
            // if dom != dom_root_ctx {
            //     // return None if dom is not an iterated ext of dom_root_ctx
            //     cwf.rows(CwfRelation::IterExtCtx).find(|r| r == &[dom_root_ctx, dom])?;
            // }

            let cod = cwf.rows(CwfRelation::Cod).find(|r| r[0] == morph).unwrap()[1];

            Some(MorphismWithSignature{
                morph: morph,
                dom: dom,
                cod: cod,
            })
        })
        .collect();

    // println!("{:?}", before_morphisms.len());

    let composition_exists: HashSet<(Element, Element)> =
        cwf.rows(CwfRelation::Comp)
        .map(|r| (r[0], r[1]))
        .collect();

    after_morphisms.into_iter()
        .zip(before_morphisms)
        // ... but only matching pairs
        .filter(|&(after, before)| after.dom == before.cod)
        // ... for which the composition doesn't exist already
        .filter(|&(after, before)| !composition_exists.contains(&(after.morph, before.morph)))
        .map(|(after, before)| {
            let comp = adjoin_op(cwf, CwfRelation::Comp, vec![after.morph, before.morph]);
            println!("Added composition {:?} o {:?}", after.morph, before.morph);
            MorphismWithSignature{
                morph: comp,
                dom: before.dom,
                cod: after.cod,
            }
        })
        .collect()
}

pub fn adjoin_post_compositions(
    cwf: &mut Cwf,
    dom_root_ctx: Element,
    after_morphisms: impl IntoIterator<Item = MorphismWithSignature>,
) {

    let mut after_morphisms: Vec<MorphismWithSignature> = after_morphisms.into_iter().collect();

    while !after_morphisms.is_empty() {
        close_cwf(cwf);
        for m in after_morphisms.iter_mut() {
            m.morph = cwf.representative(m.morph);
            m.dom = cwf.representative(m.dom);
            m.cod = cwf.representative(m.cod);
        }
        after_morphisms = adjoin_post_compositions_step(cwf, dom_root_ctx, after_morphisms);
    }
}
