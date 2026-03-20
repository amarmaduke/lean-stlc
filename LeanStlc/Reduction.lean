
import LeanSubst
import LeanSubst.Reduction
import LeanStlc.Term

open LeanSubst

inductive Red : Term -> Term -> Prop where
| beta {A b t} : Red ((:λ[A] b) :@ t) (b[.su t::+0])
| app1 {f f' a} : Red f f' -> Red (f :@ a) (f' :@ a)
| app2 {a a' f} : Red a a' -> Red (f :@ a) (f :@ a')
| lam {A t t'} : Red t t' -> Red (:λ[A] t) (:λ[A] t')
| succ : Red n n' -> Red (.succ n) (.succ n')
| nrec_zero : Red (.nrec A z s .zero) z
| nrec_succ : Red (.nrec A z s (.succ n)) (s :@ (.nrec A z s n))
| nrec1 : Red z z' -> Red (.nrec A z s n) (.nrec A z' s n)
| nrec2 : Red s s' -> Red (.nrec A z s n) (.nrec A z s' n)
| nrec3 : Red n n' -> Red (.nrec A z s n) (.nrec A z s n')

infix:80 " ~> " => Red
infix:81 " ~>* " => Star Red
infix:80 " ~s> " => ActionRed Red
infix:81 " ~s>* " => Star (ActionRed Red)

inductive ParRed : Term -> Term -> Prop where
| var {x} : ParRed (.var x) (.var x)
| zero : ParRed (.zero) (.zero)
| succ :
  ParRed n n' ->
  ParRed (.succ n) (.succ n')
| beta {A b b' t t'} :
  ParRed b b' ->
  ParRed t t' ->
  ParRed ((:λ[A] b) :@ t) (b'[.su t'::+0])
| app {f f' a a'} :
  ParRed f f' ->
  ParRed a a' ->
  ParRed (f :@ a) (f' :@ a')
| lam {t t' A} :
  ParRed t t' ->
  ParRed (:λ[A] t) (:λ[A] t')
| nrec :
  ParRed z z' ->
  ParRed s s' ->
  ParRed n n' ->
  ParRed (.nrec A z s n) (.nrec A z' s' n')
| nrec_zero :
  ParRed z z' ->
  ParRed s s' ->
  ParRed (.nrec A z s .zero) z'
| nrec_succ :
  ParRed z z' ->
  ParRed s s' ->
  ParRed n n' ->
  ParRed (.nrec A z s (.succ n)) (s' :@ (.nrec A z' s' n'))

infix:80 " ~p> " => ParRed
infix:81 " ~p>* " => Star ParRed
infix:80 " ~ps> " => ActionRed ParRed
infix:81 " ~ps>* " => Star (ActionRed ParRed)

namespace ParRed
  theorem refl {t} : t ~p> t := by
    induction t
    case var => apply ParRed.var
    case app ih1 ih2 => apply ParRed.app ih1 ih2
    case lam ih => apply ParRed.lam ih
    case _ =>
      apply ParRed.zero
    case _ ih =>
      apply ParRed.succ ih
    case _ ih1 ih2 ih3 =>
      apply nrec ih1 ih2 ih3

  @[simp]
  def complete : Term -> Term
  | .app (.lam _ b) t =>
    let b' := complete b
    let t' := complete t
    b'[.su t'::+0]
  | .app f a =>
    let f' := complete f
    let a' := complete a
    .app f' a'
  | .nrec _ z _ .zero =>
    complete z
  | .nrec A z s (.succ n) =>
    let z' := complete z
    let s' := complete s
    let n' := complete n
    s' :@ (.nrec A z' s' n')
  | .lam A t => .lam A (complete t)
  | .var x => .var x
  | .zero => .zero
  | .succ n => .succ (complete n)
  | .nrec A z s n => .nrec A (complete z) (complete s) (complete n)

  theorem subst {t t'} (σ : Subst Term) :
    t ~p> t' ->
    t[σ] ~p> t'[σ]
  := by
    intro h
    induction h generalizing σ
    case var => apply ParRed.refl
    case beta A b b' t t' r1 r2 ih1 ih2 =>
      simp; have lem1 := @ParRed.beta A (b[σ.lift]) (b'[σ.lift]) (t[σ]) (t'[σ])
      simp at lem1; apply lem1
      apply ih1; apply ih2
    case app r1 r2 ih1 ih2 =>
      simp; apply ParRed.app
      apply ih1; apply ih2
    case lam r ih =>
      simp; apply ParRed.lam; apply ih
    case _ =>
      simp; apply refl
    case _ h ih =>
      simp
      apply ParRed.succ; apply ih
    case _ h1 h2 h3 ih1 ih2 ih3 =>
      simp
      apply ParRed.nrec; apply ih1; apply ih2; apply ih3
    case _ ih1 ih2 =>
      simp
      apply ParRed.nrec_zero; apply ih1; apply ih2
    case _ ih1 ih2 ih3 =>
      simp
      apply ParRed.nrec_succ; apply ih1; apply ih2; apply ih3

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
    apply ActionRed.re
    case _ r =>
      apply ActionRed.su
      apply subst _ r

  theorem subst_red_lift {σ σ' : Subst Term} :
    (∀ x, σ x ~ps> σ' x) ->
    ∀ x, σ.lift x ~ps> σ'.lift x
  := by
    intro h x
    cases x <;> simp
    case _ => apply ActionRed.re
    case _ x =>
      have lem := subst_action (· + 1) (h x); simp at lem
      apply lem

  theorem succ_subst : n ~p> n' -> .succ n ~p> .succ n' := by
    intro h1
    apply ParRed.succ; apply h1

  theorem succ_subst2 : .succ n ~p> .succ n' -> n ~p> n' := by
    intro h1
    cases h1
    case _ j1 => apply j1

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
        have lem1 := @ParRed.beta A (b[σ.lift]) (b'[σ'.lift]) (a[σ]) (t[σ'])
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
    case _ =>
      simp
      cases h2
      simp
      apply refl
    case _ a ih =>
      simp
      cases h2
      case _ j1 => simp; apply ParRed.succ; apply ih; apply h1; apply j1
    case _ ih1 ih2 ih3 =>
      simp
      cases h2
      case _ j1 j2 j3 => simp; apply ParRed.nrec; apply ih1; apply h1; apply j1; apply ih2; apply h1; apply j2; apply ih3; apply h1; apply j3
      case _ j1 j2 => simp; apply ParRed.nrec_zero; apply ih1; apply h1; apply j2; apply ih2; apply h1; apply j1
      case _ A s z z' s' n n' j1 j2 j3 =>
        simp
        apply ParRed.nrec_succ
        case _ =>
          apply ih1; apply h1; apply j2
        case _ =>
          apply ih2; apply h1; apply j3
        case _ =>
          replace ih3 := @ih3 (.succ n') σ σ' h1 (succ_subst j1)
          apply succ_subst2; apply ih3


  theorem triangle {t s} : t ~p> s -> s ~p> complete t := by
    intro r; induction r <;> simp at *
    case var => apply ParRed.refl
    case beta ih1 ih2 =>
      apply hsubst
      intro x; cases x <;> simp
      apply ActionRed.su; apply ih2
      apply ActionRed.re; apply ih1
    case app f f' a a' r1 r2 ih1 ih2 =>
      cases f <;> simp at *
      -- case var => apply ParRed.app ih1 ih2
      -- case app => apply ParRed.app ih1 ih2
      case lam =>
        cases r1; case _ r1 =>
        cases ih1; case _ ih1 =>
        apply ParRed.beta ih1 ih2
      all_goals apply ParRed.app ih1 ih2
      -- case _ =>
      --   apply ParRed.app; apply ih1; apply ih2
      -- case _ =>
      --   apply ParRed.app; apply ih1; apply ih2
      -- case _ =>
      --   apply ParRed.app; apply ih1; apply ih2
    case lam ih => apply ParRed.lam ih
    case _ =>
      apply ParRed.zero
    case _ ih =>
      apply ParRed.succ; apply ih
    case _ n n' A h1 h2 h3 ih1 ih2 ih3 =>
      cases n
      case _ =>
        simp at ih3
        apply ParRed.nrec; apply ih1; apply ih2; simp; apply ih3
      case _ =>
        simp
        apply ParRed.nrec; apply ih1; apply ih2; apply ih3
      case _ =>
        simp
        apply ParRed.nrec ih1 ih2 ih3
      case _ =>
        simp
        cases h3
        apply ParRed.nrec_zero; apply ih1; apply ih2
      case _ =>
        simp
        cases h3; apply ParRed.nrec_succ; apply ih1; apply ih2; simp at ih3; apply succ_subst2 ih3
      case _ =>
        simp
        apply ParRed.nrec ih1 ih2 ih3
    case _ z z' s' s'' A h1 h2 ih1 ih2 =>
      apply ih1
    case _ A h1 h2 h3 ih1 ih2 ih3 =>
      apply ParRed.app ih2
      apply ParRed.nrec ih1 ih2 ih3

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
      simp; have lem1 := @Red.beta A (b[σ.lift]) (t[σ])
      simp at lem1; apply lem1
    case app1 ih =>
      simp; apply Red.app1 (ih σ)
    case app2 ih =>
      simp; apply Red.app2 (ih σ)
    case lam ih =>
      simp; apply Red.lam
      apply ih
    case _ ih1 =>
      apply Red.succ; apply ih1
    case _ =>
      simp
      apply Red.nrec_zero
    case _ =>
      simp
      apply Red.nrec_succ
    case _ h1 ih1 =>
      simp
      apply Red.nrec1
      apply ih1
    case _ ih1 =>
      simp
      apply Red.nrec2
      apply ih1
    case _ ih1 =>
      simp; apply Red.nrec3; apply ih1

  theorem subst_action {x} {σ σ' : Subst Term} (r : Ren) :
    σ x ~s> σ' x ->
    (σ ∘ r.to) x ~s> (σ' ∘ r.to) x
  := by
    intro h
    unfold Subst.compose; simp
    generalize zdef : σ x = z at *
    generalize zpdef : σ' x = z' at *
    cases z <;> cases z'
    all_goals (cases h; try simp [*])
    apply ActionRed.re
    case _ r =>
      apply ActionRed.su
      apply subst _ r

  theorem subst_red_lift {σ σ' : Subst Term} :
    (∀ x, σ x ~s> σ' x) ->
    ∀ x, σ.lift x ~s> σ'.lift x
  := by
    intro h x
    cases x <;> simp
    case _ => apply ActionRed.re
    case _ x =>
      have lem := subst_action (· + 1) (h x); simp at lem
      apply lem

  theorem seq_implies_par {t t'} : t ~> t' -> t ~p> t' := by
    intro h; induction h
    case beta => apply ParRed.beta ParRed.refl ParRed.refl
    case app1 r ih => apply ParRed.app ih ParRed.refl
    case app2 r ih => apply ParRed.app ParRed.refl ih
    case lam r ih => apply ParRed.lam ih
    case _ ih1 =>
      constructor; assumption
    case _ A z s =>
      apply ParRed.nrec_zero (z := z) (s' := s)
      case _ =>
        apply ParRed.refl
      case _ =>
        apply ParRed.refl
    case _ =>
      apply ParRed.nrec_succ; apply ParRed.refl; apply ParRed.refl; apply ParRed.refl
    case _ h1 ih1 =>
      apply ParRed.nrec; apply ih1; apply ParRed.refl; apply ParRed.refl
    case _ h1 ih1 =>
      apply ParRed.nrec (ParRed.refl) ih1 (ParRed.refl)
    case _ =>
      apply ParRed.nrec (ParRed.refl) (ParRed.refl); assumption

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
    case _ =>
      constructor
    case _ ih =>
      apply Star.congr1; intro t t'; intro h1; apply Red.succ h1
      apply ih
    case _ z z' s s' n n' A h1 h2 h3 ih1 ih2 ih3 =>
      apply Star.congr3; intro t1 t2 t3 t1' j1; apply Red.nrec1 j1; intro t2 t3 t3' t2' j1; apply Red.nrec2 j1; intro t2 t3 t3' t3'' j1; apply Red.nrec3 j1
      apply ih1; apply ih2; apply ih3
    case _ z z' s s' A h1 h2 ih1 ih2 =>
      apply Star.trans; apply Star.step; apply Star.refl; apply Red.nrec_zero; apply ih1
    case _ z z' s s' n n' A h1 h2 h3 ih1 ih2 ih3 =>
      apply Star.trans (y := s :@ Term.nrec A z s n); apply Star.step; apply Star.refl; apply Red.nrec_succ;
      apply Star.trans (y := s :@ (Term.nrec A z' s' n')); apply Star.congr2; intro t1 t2 t1' j1
      apply Red.app1 j1; intro t1 t2 t2' j1; apply Red.app2 j1; apply Star.refl; apply Star.congr3; intro t1 t2 t3 t1' j1; apply Red.nrec1 j1
      intro t1 t2 t3 t2' j1; apply Red.nrec2 j1; intro t1 t2 t3 t3' j1; apply Red.nrec3 j1; apply ih1; apply ih2; apply ih3
      apply Star.congr2; intro t1 t2 t1' j1; apply Red.app1 j1; intro t1 t2 t2' j1; apply Red.app2 j1; apply ih2; apply Star.refl

  theorem pars_implies_seqs {t t'} : t ~p>* t' -> t ~>* t' := by
    intro h; induction h
    case _ => apply Star.refl
    case _ y z r1 r2 ih =>
      replace r2 := par_implies_seqs r2
      apply Star.trans ih r2

  theorem pars_action_lift : t ~p>* t' -> .su t ~ps>* .su t' := by
    intro r; induction r
    case _ => apply Star.refl
    case _ r1 r2 ih =>
      apply Star.step ih
      apply ActionRed.su r2

  theorem seqs_action_lift : t ~>* t' -> .su t ~s>* .su t' := by
    intro r; induction r
    case _ => apply Star.refl
    case _ r1 r2 ih =>
      apply Star.step ih
      apply ActionRed.su r2

  theorem seqs_action_destruct : a ~s>* .su t' -> ∃ t, a = .su t ∧ t ~>* t' := by
    intro r
    generalize zdef : Subst.Action.su t' = z at r
    induction r generalizing t'
    case _ =>
      subst zdef; exists t'; simp
      apply Star.refl
    case _ r1 r2 ih =>
      subst zdef; cases r2
      case _ t r2 =>
        replace ih := @ih t rfl
        cases ih; case _ z ih =>
        cases ih; case _ e ih =>
        subst e; exists z; apply And.intro rfl
        apply Star.step ih r2

  theorem pars_action_iff_seqs_action : t ~ps>* t' <-> t ~s>* t' := by
    apply Iff.intro
    case _ =>
      intro h; induction h
      case _ => apply Star.refl
      case _ r1 r2 ih =>
        cases r2
        case _ r2 =>
          have lem := seqs_action_destruct ih
          cases lem; case _ z lem =>
          cases lem; case _ e lem =>
          subst e
          replace r2 := par_implies_seqs r2
          apply Star.trans ih
          apply seqs_action_lift r2
        case _ => apply ih
    case _ =>
      intro h; induction h
      case _ => apply Star.refl
      case _ r1 r2 ih =>
        cases r2
        case _ r2 =>
          replace r1 := seqs_action_destruct r1
          cases r1; case _ z r1 =>
          cases r1; case _ e r1 =>
          subst e; replace r2 := Star.step r1 r2
          replace r2 := seqs_implies_pars r2
          apply pars_action_lift r2
        case _ => apply ih

  theorem subst_arg {t} {σ σ' : Subst Term} :
    (∀ x, σ x ~s> σ' x) ->
    t[σ] ~>* t[σ']
  := by
    intro h
    induction t generalizing σ σ' <;> simp at *
    case _ x =>
      generalize zdef : σ x = z at *
      generalize wdef : σ' x = w at *
      cases z
      case _ t =>
        replace h := h x; rw [zdef] at h
        rw [wdef] at h; cases h; simp
        apply Star.refl
      case _ t =>
        replace h := h x; rw [zdef] at h
        rw [wdef] at h; cases h; simp
        case _ t' r =>
        apply Star.step Star.refl r
    case _ ih1 ih2 =>
      apply Star.congr2 Term.app Red.app1 Red.app2 (ih1 h) (ih2 h)
    case _ A a ih =>
      have lem := subst_red_lift h
      replace ih := ih lem
      have lem2 := Star.congr1 (t1 := a[σ.lift]) (t1' := a[σ'.lift]) (:λ[A] ·) (@Red.lam A) ih
      simp at lem2; apply lem2
    case _ =>
      apply Star.refl
    case _ t ih =>
      apply Star.congr1; intro t t' h2; apply Red.succ h2
      apply ih h
    case _ A t t' t'' ih1 ih2 ih3 =>
      apply Star.congr3; intro t1 t2 t3 t1' h1; apply Red.nrec1 h1; intro t1 t2 t3 t2' h2; apply Red.nrec2 h2
      intro t1 t2 t3 t3' h1; apply Red.nrec3 h1; apply ih1 h; apply ih2 h; apply ih3 h

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

  theorem preservation_of_neutral_step : Neutral t -> t ~> t' -> Neutral t' := by
    sorry
    -- intro h r
    -- induction h generalizing t'
    -- case _ => cases r
    -- case _ f a h ih =>
    --   cases r
    --   case _ => cases h
    --   case _ f' r => apply Neutral.app (ih r)
    --   case _ a' r => apply Neutral.app h

  theorem preservation_of_neutral : Neutral t -> t ~>* t' -> Neutral t' := by
    intro h r
    induction r
    case _ => apply h
    case _ r1 r2 ih =>
      apply preservation_of_neutral_step ih r2
end Red
