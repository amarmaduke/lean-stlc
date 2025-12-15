import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.Progress

open LeanSubst

inductive SnHeadRed : Term -> Term -> Prop where
| beta {t A b} : SN Red t -> SnHeadRed ((:λ[A] b) :@ t) (b[.su t::+0])
| app {f f'} a : SnHeadRed f f' -> SnHeadRed (f :@ a) (f' :@ a)

infix:80 " ~>sn " => SnHeadRed

namespace SnHeadRed
  theorem red_compatible {t a b} : t ~>sn a -> t ~> b -> a = b ∨ ∃ z, b ~>sn z ∧ a ~>* z := by
    intro r1 r2
    induction r1 generalizing b
    case _ t' A b' h =>
      cases r2
      case _ => apply Or.inl rfl
      case _ f' r =>
        cases r; case _ b'' r =>
        apply Or.inr; exists (b''[.su t' :: +0])
        apply And.intro
        apply SnHeadRed.beta h
        apply Star.subst; apply Star.step Star.refl r
      case _ t'' r =>
        apply Or.inr; exists (b'[.su t'' :: +0])
        apply And.intro
        apply SnHeadRed.beta
        apply SN.preservation_step h r
        apply Red.subst_arg
        intro x; cases x <;> simp
        case _ => apply ActionRed.su r
        case _ => apply ActionRed.re
    case _ f f' a r1 ih =>
      cases r2
      case _ => cases r1
      case _ f'' r2 =>
        replace ih := ih r2
        cases ih
        case _ ih =>
          subst ih; apply Or.inl rfl
        case _ ih =>
          cases ih; case _ z ih =>
          have lem1 := SnHeadRed.app a ih.1
          apply Or.inr
          exists (z :@ a); apply And.intro lem1
          apply Star.congr2_1 a Term.app Red.app1 ih.2
      case _ a'' r2 =>
        apply Or.inr
        exists (f' :@ a''); apply And.intro
        apply SnHeadRed.app a'' r1
        apply Star.congr2_2 f' Term.app Red.app2
        apply Star.step Star.refl r2
end SnHeadRed

namespace SN
  theorem subterm_app {f a} : SN Red (f :@ a) -> SN Red f ∧ SN Red a := by
    intro h
    generalize zdef : f :@ a = z at *
    induction h generalizing f a
    case _ x h ih =>
    apply And.intro
    case _ =>
      apply SN.sn; intro y r
      subst zdef
      replace ih := ih (y :@ a) (Red.app1 r) rfl
      apply ih.1
    case _ =>
      apply SN.sn; intro y r
      subst zdef
      replace ih := ih (f :@ y) (Red.app2 r) rfl
      apply ih.2

  theorem lam {t A} : SN Red t <-> SN Red (:λ[A] t) := by
    apply Iff.intro
    case _ =>
      intro h; induction h
      case _ t h ih =>
      apply SN.sn; intro y r
      cases r; case _ t' r =>
      apply ih _ r
    case _ =>
      intro h
      generalize zdef : (:λ[A] t) = z at *
      induction h generalizing t
      case _ x h ih =>
      apply SN.sn; intro y r
      subst zdef
      apply ih (:λ[A] y) (Red.lam r) rfl

  theorem neutral_app {f a} : Neutral f -> SN Red f -> SN Red a -> SN Red (f :@ a) := by
    intro h1 h2 h3
    induction h2 generalizing a
    case _ f h2 ih2 =>
      induction h3
      case _ a h3 ih3 =>
      apply SN.sn; intro y r
      cases r
      case _ => cases h1
      case _ f' r =>
        have lem1 := Red.preservation_of_neutral_step h1 r
        have lem2 : SN Red a := SN.sn h3
        apply ih2 f' r lem1 lem2
      case _ a' r =>
        apply ih3 a' r

  theorem weak_head_expansion {t b A}

    : SN Red t -> SN Red (b[.su t::+0]) -> SN Red ((:λ[A] b) :@ t)
  := by
    intro h1; induction h1 generalizing b
    case _ t h1 ih1 =>
    intro h2
    generalize zdef : b[.su t :: +0] = z at *
    induction h2 generalizing b
    case _ w h2 ih2 =>
    apply SN.sn; intro y r
    cases r
    case _ => rw [zdef]; apply SN.sn h2
    case _ q r =>
      cases r; case _ b' r =>
      have lem : b[.su t::+0] ~> b'[.su t::+0] := by
        apply Red.subst (.su t::+0) r
      apply ih2 (b'[.su t::+0]) (by rw [<-zdef]; apply lem) rfl
    case _ t' r =>
      have lem1 : SN Red w := SN.sn h2; rw [<-zdef] at lem1
      have lem2 : b[.su t::+0] ~>* b[.su t'::+0] := by
        apply Red.subst_arg; intro x
        cases x <;> simp at *
        apply ActionRed.su r
        apply ActionRed.re
      have lem3 := SN.preservation lem1 lem2
      apply ih1 t' r lem3

  theorem red_app_preservation {f f' a}
    : f ~>sn f' -> SN Red f -> SN Red a -> SN Red (f' :@ a) -> SN Red (f :@ a)
  := by
    intro r1 h1 h2 h3
    induction h1 generalizing f' a
    case _ f h1 ih1 =>
    induction h2
    case _ a h2 ih2 =>
    apply SN.sn; intro y r2
    cases r2
    case _ => cases r1
    case _ f'' r =>
      have lem1 := SnHeadRed.red_compatible r1 r
      cases lem1
      case _ lem1 => subst lem1; apply h3
      case _ lem1 =>
        cases lem1; case _ z lem1 =>
        apply ih1 f'' r lem1.1 (SN.sn h2)
        apply SN.preservation h3
        apply Star.congr2_1 a Term.app Red.app1 lem1.2
    case _ a'' r =>
      apply ih2 a'' r
      apply SN.preservation h3
      apply Star.congr2_2 f' Term.app Red.app2 (Star.step Star.refl r)

  theorem backward_closure {t' t} : SN Red t' -> t ~>sn t' -> SN Red t := by
    intro h r; induction r
    case _ h2 => apply weak_head_expansion h2 h
    case _ r ih =>
      have lem := subterm_app h
      apply red_app_preservation r (ih lem.1) lem.2 h
end SN

inductive SnVariant where
| neu | nor | red

@[simp]
abbrev SnIndices : SnVariant -> Type
| .neu => Term
| .nor => Term
| .red => (Term) × (Term)

inductive SNi : (v : SnVariant) -> SnIndices v -> Prop where
| var {x} : SNi .neu (.var x)
| app {s t} :
  SNi .neu s ->
  SNi .nor t ->
  SNi .neu (s :@ t)
| lam {t A} :
  SNi .nor t ->
  SNi .nor (:λ[A] t)
| neu {t} :
  SNi .neu t ->
  SNi .nor t
| red {t t'} :
  SNi .red (t, t') ->
  SNi .nor t' ->
  SNi .nor t
| beta {t A b} :
  SNi .nor t ->
  SNi .red ((:λ[A] b) :@ t, b[.su t :: +0])
| step {s s' t} :
  SNi .red (s, s') ->
  SNi .red (s :@ t, s' :@ t)

namespace SNi
  @[simp]
  abbrev SnRenameLemmaType (r : Ren) : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, t => SNi .neu (t[r])
  | .nor, t => SNi .nor (t[r])
  | .red, (t, t') => SNi .red (t[r], t'[r])

  theorem rename {v i} r : SNi v i -> SnRenameLemmaType r v i := by
    intro j; induction j generalizing r <;> simp at *
    case var x => apply SNi.var
    case app i1 i2 j1 j2 ih1 ih2 =>
      apply SNi.app <;> simp [*]
    case lam t A j ih =>
      apply SNi.lam
      replace ih := ih r.lift
      simp at ih
      rw [Ren.to_lift] at ih
      simp at ih
      apply ih
    case neu t j ih =>
      apply SNi.neu; simp [*]
    case red t t' j1 j2 ih1 ih2 =>
      apply SNi.red (ih1 r) (ih2 r)
    case beta t A b j ih =>
      have lem := @SNi.beta (t[r]) A (b[.re 0 :: r ∘ +1]) (ih r); simp at lem
      apply lem
    case step s s' t j ih =>
      apply SNi.step; simp [*]

  @[simp]
  abbrev SnAntiRenameLemmaType (r : Ren) : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, t => ∀ z, t = z[r] -> SNi .neu z
  | .nor, t => ∀ z, t = z[r] -> SNi .nor z
  | .red, (t, t') =>
    ∀ z, t = z[r] ->
    ∃ z', t' = z'[r] ∧ SNi .red (z, z')

  theorem antirename {v i} r : SNi v i -> SnAntiRenameLemmaType r v i := by
    intro j; induction j generalizing r <;> simp at *
    case var x =>
      intro z h
      cases z <;> simp at h
      case _ y => apply SNi.var
    case app s t j1 j2 ih1 ih2 =>
      intro z h1; cases z <;> simp at h1
      case _ x => apply SNi.var
      case _ u v => apply SNi.app (ih1 r _ h1.1) (ih2 r _ h1.2)
    case lam t A j ih =>
      intro z h
      cases z <;> simp at h
      case _ x => apply SNi.neu; apply SNi.var
      case _ A' b =>
        cases h; case _ h1 h2 =>
        subst h1; apply SNi.lam
        replace ih := ih (r.lift) b
        rw [Ren.to_lift] at ih
        simp at ih; apply ih h2
    case neu t j ih =>
      intro z h2
      replace ih := ih r z h2
      apply SNi.neu ih
    case red t t' j1 j2 ih1 ih2 =>
      intro z h2
      have lem := ih1 r _ h2
      cases lem; case _ z' h2 =>
      apply SNi.red h2.2
      apply ih2 r _ h2.1
    case beta t A b j ih =>
      intro z h2
      cases z <;> simp at h2
      case _ x =>
        have lem := to_ren_is_var h2
        cases lem; case _ y lem =>
        injection lem
      case _ u v =>
        cases u <;> simp at h2
        case _ x =>
          have lem := to_ren_is_var h2.1
          cases lem; case _ y lem =>
          injection lem
        case _ A' u =>
          cases h2; case _ h1 h2 =>
          cases h1; case _ h1 h3 =>
          subst h1
          replace ih := ih r _ h2
          subst h2; subst h3; simp at *
          exists (u[.su v :: +0]); simp
          apply SNi.beta ih
    case step s s' t j ih =>
      intro z h2
      cases z <;> simp at h2
      case _ x =>
        have lem := to_ren_is_var h2
        cases lem; case _ y lem =>
        injection lem
      case _ u v =>
        replace ih := ih r _ h2.1
        cases ih; case _ z' h' =>
        exists (z' :@ v); simp [*]
        apply SNi.step (h'.2)

  @[simp]
  abbrev SnBetaVarLemmaType : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, s => ∀ t x, s = t :@ .var x -> SNi .neu t
  | .nor, s => ∀ t x, s = t :@ .var x -> SNi .nor t
  | .red, _ => True

  theorem beta_var {v i} : SNi v i -> SnBetaVarLemmaType v i := by
    intro j; induction j <;> simp at *
    case app s t j1 j2 ih1 ih2 =>
      intro u x e1 e2; subst e1; subst e2
      apply j1
    case neu t j ih =>
      intro u x e
      cases t <;> simp at e
      case _ v w =>
      cases e; case _ e1 e2 =>
      subst e1; subst e2
      cases j; case _ j1 j2 =>
      apply SNi.neu j1
    case red t t' j1 j2 ih1 ih2 =>
      intro u x e
      cases t <;> simp at e
      case _ v w =>
      cases e; case _ e1 e2 =>
      subst e1; subst e2
      cases j1
      case beta A b j1 =>
        let r : Ren := x :: id
        have lem : b[.su (.var x) :: +0] = b[r] := by
          subst r; rw [ren_subst_apply_eq]
          intro i y h
          cases i <;> simp at *
          case zero => exact h
          case _ z => apply Or.inl; exact h
        rw [lem] at j2
        apply SNi.lam
        apply @antirename .nor (b[r]) r j2
        rfl
      case step s' j1 =>
        replace ih2 := ih2 s' x rfl
        apply SNi.red j1 ih2

  @[simp]
  abbrev SnPropertyWeakenLemmaType : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, s => Neutral s
  | .nor, _ => True
  | .red, (s, t) => s ~> t

  theorem property_weaken {v i} : SNi v i -> SnPropertyWeakenLemmaType v i := by
    intro h
    induction h <;> simp at *
    case _ => apply Neutral.var
    case _ ih _ => apply Neutral.app ih
    case _ => apply Red.beta
    case _ ih => apply Red.app1 ih

  @[simp]
  abbrev SnSoundLemmaType : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, s => SN Red s
  | .nor, s => SN Red s
  | .red, (s, t) => s ~>sn t

  theorem sound {v i} : SNi v i -> SnSoundLemmaType v i := by
    intro h; induction h <;> simp at *
    case _ => apply SN.sn; intro y r; cases r
    case _ s t j1 j2 ih1 ih2 =>
      have lem := property_weaken j1; simp at lem
      apply SN.neutral_app lem ih1 ih2
    case _ t A j ih => apply SN.lam.1 ih
    case _ t j ih => apply ih
    case _ ih1 ih2 => apply SN.backward_closure ih2 ih1
    case _ ih => apply SnHeadRed.beta ih
    case _ ih => apply SnHeadRed.app _ ih

  -- TODO: prove completeness
  -- theorem complete {t} : (SN Red t -> SNi .nor t) ∧ (∀ t', t ~>sn t' -> SNi .red (t, t')) := by
  --   induction t
  --   case _ x =>
  --     apply And.intro
  --     intro h; apply SNi.neu (SNi.var)
  --     intro t' h; cases h
  --   case _ f a ih1 ih2 =>
  --     apply And.intro
  --     case _ =>
  --       intro h
  --       have lem1 := sn_subterm_app h
  --       have lem2 := ih1.1 lem1.1
  --       cases lem2
  --       case _ j =>
  --         sorry
  --       case _ h => apply SNi.neu (SNi.app h (ih2.1 lem1.2))
  --       case _ t' j1 j2 =>
  --         have lem : SNi .red (f :@ a, t' :@ a) := by sorry
  --         apply SNi.red lem
  --         sorry
  --     case _ =>
  --       intro t' r; cases r
  --       case _ A b h =>
  --         apply SNi.beta
  --         apply ih2.1 h
  --       case _ f' r =>
  --         apply SNi.step
  --         apply ih1.2 f' r
  --   case _ A t ih =>
  --     apply And.intro
  --     intro h; apply SNi.lam
  --     apply ih.1 (sn_lam.2 h)
  --     intro t' r; cases r
end SNi
