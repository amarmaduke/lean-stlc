
import LeanSubst
import LeanSubst.Reduction
import LeanStlc.Term

open LeanSubst

inductive Red : Term -> Term -> Prop where
| beta {A b t} : Red ((:λ[A] b) :@ t) (b[.su t::I])
| app1 {f f' a} : Red f f' -> Red (f :@ a) (f' :@ a)
| app2 {a a' f} : Red a a' -> Red (f :@ a) (f :@ a')
| lam {A t t'} : Red t t' -> Red (:λ[A] t) (:λ[A] t')

infix:80 " ~> " => Red
infix:81 " ~>* " => Star Red

inductive ParRed : Term -> Term -> Prop where
| var {x} : ParRed #x #x
| beta {A b b' t t'} :
  ParRed b b' ->
  ParRed t t' ->
  ParRed ((:λ[A] b) :@ t) (b'[.su t'::I])
| app {f f' a a'} :
  ParRed f f' ->
  ParRed a a' ->
  ParRed (f :@ a) (f' :@ a')
| lam {t t' A} :
  ParRed t t' ->
  ParRed (:λ[A] t) (:λ[A] t')

infix:80 " ~p> " => ParRed
infix:81 " ~p>* " => Star ParRed

inductive ParRedSubstAction : Subst.Action Term -> Subst.Action Term -> Prop where
| su {t t'} : t ~p> t' -> ParRedSubstAction (.su t) (.su t')
| re {x} : ParRedSubstAction (.re x) (.re x)

infix:80 " ~ps> " => ParRedSubstAction
infix:81 " ~ps>* " => Star ParRedSubstAction

namespace ParRed
  theorem refl {t} : t ~p> t := by
    induction t
    case var => apply ParRed.var
    case app ih1 ih2 => apply ParRed.app ih1 ih2
    case lam ih => apply ParRed.lam ih

  @[simp]
  def complete : Term -> Term
  | .app (.lam _ b) t =>
    let b' := complete b
    let t' := complete t
    b'[.su t'::I]
  | .app f a =>
    let f' := complete f
    let a' := complete a
    .app f' a'
  | .lam A t => .lam A (complete t)
  | .var x => .var x

  theorem subst {t t'} (σ : Subst Term) :
    t ~p> t' ->
    t[σ] ~p> t'[σ]
  := by
    intro h
    induction h generalizing σ
    case var => apply ParRed.refl
    case beta A b b' t t' r1 r2 ih1 ih2 =>
      simp; have lem1 := @ParRed.beta A
        (b[.re 0 :: σ ∘ S]) (b'[.re 0 :: σ ∘ S])
        (t[σ]) (t'[σ])
      simp at lem1; apply lem1
      apply ih1; apply ih2
    case app r1 r2 ih1 ih2 =>
      simp; apply ParRed.app
      apply ih1; apply ih2
    case lam r ih =>
      simp; apply ParRed.lam; apply ih

  theorem subst_action {x} {σ σ' : Subst Term} (r : Ren) :
    σ x ~ps> σ' x ->
    (σ ∘ r.to) x ~ps> (σ' ∘ r.to) x
  := by
    intro h
    unfold Subst.compose; simp
    generalize zdef : σ x = z at *
    generalize zpdef : σ' x = z' at *
    cases z <;> cases z'
    all_goals (cases h; try simp [*])
    apply ParRedSubstAction.re
    case _ r =>
      apply ParRedSubstAction.su
      apply subst _ r

  theorem subst_red_lift {σ σ' : Subst Term} :
    (∀ x, σ x ~ps> σ' x) ->
    ∀ x, σ.lift x ~ps> σ'.lift x
  := by
    intro h x
    cases x <;> simp
    case _ => apply ParRedSubstAction.re
    case _ x =>
      have lem := subst_action (· + 1) (h x); simp at lem
      apply lem

  theorem hsubst {t t'} {σ σ' : Subst Term} :
    (∀ x, σ x ~ps> σ' x) ->
    t ~p> t' ->
    t[σ] ~p> t'[σ']
  := by
    intro h1 h2; induction t generalizing t' σ σ'
    case var x =>
      cases h2; simp
      replace h1 := h1 x
      generalize zdef : σ x = z at *
      generalize zpdef : σ' x = z' at *
      cases z <;> cases z'
      all_goals (cases h1; try simp [*])
      apply refl
    case app f a ih1 ih2 =>
      cases h2 <;> simp at *
      case beta A b b' t r1 r2 =>
        have lem1 := @ParRed.beta A (b[.re 0 :: σ ∘ S]) (b'[.re 0 :: σ' ∘ S]) (a[σ]) (t[σ'])
        simp at lem1; apply lem1 _
        apply ih2 h1 r2
        have lem2 := ih1 h1 (ParRed.lam r1); simp at lem2
        cases lem2; case _ lem2 =>
        apply lem2
      case app f' a' r1 r2 =>
        apply ParRed.app
        apply ih1 h1 r1
        apply ih2 h1 r2
    case lam t ih =>
      cases h2; case _ t' h2 =>
      simp; apply ParRed.lam
      have lem := @ih t' σ.lift σ'.lift (subst_red_lift h1) h2
      simp at lem; apply lem

  theorem triangle {t s} : t ~p> s -> s ~p> complete t := by
    intro r; induction r <;> simp at *
    case var => apply ParRed.refl
    case beta ih1 ih2 =>
      apply hsubst
      intro x; cases x <;> simp
      apply ParRedSubstAction.su; apply ih2
      apply ParRedSubstAction.re; apply ih1
    case app f f' a a' r1 r2 ih1 ih2 =>
      cases f <;> simp at *
      case var => apply ParRed.app ih1 ih2
      case app => apply ParRed.app ih1 ih2
      case lam =>
        cases r1; case _ r1 =>
        cases ih1; case _ ih1 =>
        apply ParRed.beta ih1 ih2
    case lam ih => apply ParRed.lam ih

  instance : Substitutive ParRed where
    subst := subst

  instance : HasTriangle ParRed where
    complete := complete
    triangle := triangle
end ParRed

namespace Red
  theorem subst {t t'} (σ : Subst Term) :
    t ~> t' ->
    t[σ] ~> t'[σ]
  := by
    intro h
    induction h generalizing σ
    case beta A b t =>
      simp; have lem1 := @Red.beta A (b[.re 0 :: σ ∘ S]) (t[σ])
      simp at lem1; apply lem1
    case app1 ih =>
      simp; apply Red.app1 (ih σ)
    case app2 ih =>
      simp; apply Red.app2 (ih σ)
    case lam ih =>
      simp; apply Red.lam
      apply ih

  theorem seq_implies_par {t t'} : t ~> t' -> t ~p> t' := by
    intro h; induction h
    case beta => apply ParRed.beta ParRed.refl ParRed.refl
    case app1 r ih => apply ParRed.app ih ParRed.refl
    case app2 r ih => apply ParRed.app ParRed.refl ih
    case lam r ih => apply ParRed.lam ih

  theorem seqs_implies_pars {t t'} : t ~>* t' -> t ~p>* t' := by
    intro h; induction h
    case _ => apply Star.refl
    case _ y z r1 r2 ih =>
      replace r2 := seq_implies_par r2
      apply Star.step ih r2

  theorem par_implies_seqs {t t'} : t ~p> t' -> t ~>* t' := by
    intro h; induction h
    case var => apply Star.refl
    case beta A b b' q q' r1 r2 ih1 ih2 =>
      have lem : (:λ[A] b) ~>* (:λ[A] b') := by
        apply Star.congr1 (Term.lam A) (@Red.lam A) ih1
      apply Star.trans
      apply Star.congr2 Term.app Red.app1 Red.app2 lem ih2
      apply Star.step Star.refl
      apply Red.beta
    case app f f' a a' r1 r2 ih1 ih2 =>
      apply Star.congr2 Term.app Red.app1 Red.app2 ih1 ih2
    case lam t t' A r ih =>
      apply Star.congr1 (Term.lam A) (@Red.lam A) ih

  theorem pars_implies_seqs {t t'} : t ~p>* t' -> t ~>* t' := by
    intro h; induction h
    case _ => apply Star.refl
    case _ y z r1 r2 ih =>
      replace r2 := par_implies_seqs r2
      apply Star.trans ih r2

  theorem confluence {s t1 t2} : s ~>* t1 -> s ~>* t2 -> ∃ t, t1 ~>* t ∧ t2 ~>* t := by
    intro h1 h2
    have lem1 := seqs_implies_pars h1
    have lem2 := seqs_implies_pars h2
    have lem3 := HasConfluence.confluence lem1 lem2
    cases lem3; case _ w lem3 =>
    have lem4 := pars_implies_seqs lem3.1
    have lem5 := pars_implies_seqs lem3.2
    exists w

  instance : Substitutive Red where
    subst := subst

  instance : HasConfluence Red where
    confluence := confluence
end Red
