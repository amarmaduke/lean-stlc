import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.SNi

open LeanSubst

namespace StrongNormalizaton
  @[simp]
  def LR : Ty -> (Term -> Prop)
  | .base => λ t => SNi .nor t
  | .arrow A B => λ t => ∀ (r : Ren) (v : Term), LR A v -> LR B (t[r] :@ v)

  @[simp]
  def GR : List Ty -> (Subst Term -> Prop)
  | Γ, σ => ∀ x T, Γ[x]? = .some T -> LR T ↑(σ x)

  @[simp]
  def SemanticTyping Γ t A := ∀ σ, GR Γ σ -> LR A (t[σ])

  notation:170 Γ:170 " ⊨s " t:170 " : " A:170 => SemanticTyping Γ t A

  theorem monotone {A t} (r : Ren) : LR A t -> LR A (t[r]) := by
    intro h; induction A generalizing t r
    case _ =>
      simp at *
      apply SNi.rename r h
    case _ A B ih1 ih2 =>
      simp at *; intro r' v rh
      replace h := h (r' ∘ r) v rh
      simp at h; apply h

  theorem cr {A} :
    (∀ t, LR A t -> SNi .nor t)
    ∧ (∀ t, SNi .neu t -> LR A t)
    ∧ (∀ t t', SNi .red (t, t') -> LR A t' -> LR A t)
  := by
    induction A <;> simp at *
    case _ =>
      apply And.intro _ _
      apply SNi.neu
      apply SNi.red
    case _ A B ih1 ih2 =>
      apply And.intro
      case _ =>
        intro t h
        apply @SNi.antirename .nor (t[Ren.to (· + 1)]) (· + 1) _ t rfl
        apply @SNi.beta_var .nor _ _ _ 0 rfl
        replace h := h (· + 1) (.var 0) (ih1.2.1 (.var 0) SNi.var); simp at h
        apply ih2.1 _ h
      case _ =>
        apply And.intro
        case _ =>
          intro t h r v lr
          apply ih2.2.1
          apply SNi.app
          apply SNi.rename r h
          apply ih1.1 _ lr
        case _ =>
          intro t t' h1 h2 r v lr
          have lem1 := h2 r v lr
          apply ih2.2.2 (t[r] :@ v) (t'[r] :@ v) _ lem1
          replace h1 := SNi.rename r h1; simp at h1
          apply SNi.step h1

  theorem var {A x} : LR A (.var x) := by
    apply cr.2.1; apply SNi.var

  theorem fundamental {Γ t A} : Γ ⊢ t : A -> Γ ⊨s t : A := by
    intro j; induction j
    case var Γ T x j =>
      simp; intro σ h
      apply h x T j
    case app Γ A B f a j1 j2 ih1 ih2 =>
      simp; intro σ h; simp at ih1
      replace ih1 := ih1 σ h id (a[σ])
      simp at ih1; apply ih1
      apply ih2 σ h
    case lam Γ A B t j ih =>
      simp; intro σ h r v lv
      have lem : t[.re 0::σ ∘ r ∘ +1][.su v :: +0] = t[.su v::σ ∘ r.to] := by simp
      apply cr.2.2 _ (t[.su v::σ ∘ r.to])
      have lem2 := @SNi.beta v A (t[.re 0::σ ∘ r ∘ +1]); simp at lem2
      apply lem2
      apply cr.1 _ lv
      replace ih := ih (.su v :: σ ∘ r.to)
      apply ih
      simp; intro x T j2
      cases x
      case _ =>
        simp; simp at j2; subst j2
        apply lv
      case _ x =>
        simp; simp at j2
        replace h := h x T j2
        unfold Subst.compose; simp
        generalize zdef : σ x = z at *
        cases z <;> simp at *
        case _ k =>
          have lem := monotone r h; simp at lem
          generalize wdef : r k = w at *
          cases w <;> simp [*]
        case _ t => apply monotone r h
end StrongNormalizaton

theorem strong_normalization_inductive {Γ t A} : Γ ⊢ t : A -> SNi .nor t := by
  intro j
  have lem1 : StrongNormalizaton.GR Γ +0 := by
    simp; intro x T h
    apply StrongNormalizaton.var
  have lem2 := StrongNormalizaton.fundamental j +0 lem1; simp at lem2
  apply StrongNormalizaton.cr.1 _ lem2

theorem strong_normalization {Γ t A} : Γ ⊢ t : A -> SN Red t := by
  intro j; apply @SNi.sound .nor t
  apply strong_normalization_inductive j
