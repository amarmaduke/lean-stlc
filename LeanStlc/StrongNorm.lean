import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.Preservation
import LeanStlc.SNi

open LeanSubst

namespace StrongNormalizaton

  @[simp]
  def LR (Γ : List Ty) : Ty -> (Term -> Prop)
  | .base => λ t => Γ ⊢ t : .base ∧ SnNor t
  | .arrow A B => λ t => Γ ⊢ t : (A -t> B)
    ∧ ∀ {r Δ v}, Γ -⟨r⟩> Δ -> LR Δ A v -> LR Δ B (t[r] :@ v)
  | .nat => λ t => Γ ⊢ t : Ty.nat ∧ SnNor t

  @[simp]
  def GR : List Ty -> List Ty -> (Subst Term -> Prop)
  | Γ, Δ, σ => ∀ x T, Γ[x]? = .some T -> LR Δ T ↑(σ x)

  @[simp]
  def SemanticTyping Γ t A := ∀ σ Δ, GR Γ Δ σ -> LR Δ A (t[σ])

  notation:170 Γ:170 " ⊨s " t:170 " : " A:170 => SemanticTyping Γ t A

  theorem LR.typing : LR Γ A t -> Γ ⊢ t : A := by
    intro j; induction A generalizing Γ t
    all_goals simp at j; grind

  theorem LR.monotone (m : Γ -⟨r⟩> Δ) : LR Γ A t -> LR Δ A (t[r]) := by
    intro h; induction A generalizing Γ Δ t r
    case arrow A B ih1 ih2 =>
      apply And.intro
      apply Typing.rename m (typing h)
      intro r' Δ' v m' lv
      replace h := h.2 (m' ∘ m) lv
      simp; exact h
    all_goals
      simp at *; constructor
      apply Typing.rename m h.1
      apply SnNor.rename r h.2

  theorem GR.forget : GR Γ Δ σ -> Γ -[σ]> Δ := by
    intro h1 x T h2
    replace h1 := h1 x T h2
    apply LR.typing h1

  theorem cr :
    (∀ {Γ t}, LR Γ A t -> SnNor t)
    ∧ (∀ {Γ t}, Γ ⊢ t : A -> SnNeu t -> LR Γ A t)
    ∧ (∀ {Γ t t'}, Γ ⊢ t : A -> SnRed t t' -> LR Γ A t' -> LR Γ A t)
  := by
    induction A <;> simp at *
    case arrow A B ih1 ih2 =>
      apply And.intro
      case _ =>
        intro Γ t j h
        apply @SnNor.antirename (t[Ren.to (· + 1)]) (· + 1) _ t rfl
        apply @SnNor.beta_var _ _ _ 0 rfl
        replace h := h TypingRen.succ (@ih1.2.1 (A::Γ) #0 (.var (by simp)) .var)
        simp at h
        apply ih2.1 h
      case _ =>
        apply And.intro
        case _ =>
          intro Γ t j h
          apply And.intro j
          intro r Δ v m lv
          apply ih2.2.1
          apply Typing.app _ (LR.typing lv); apply Typing.rename m j
          apply SnNeu.app
          apply SnNeu.rename r h
          apply ih1.1 lv
        case _ =>
          intro Γ t t' j1 h1 j2 h2
          apply And.intro j1
          intro r Δ v m lv
          have lem1 := h2 m lv
          apply @ih2.2.2 _ (t[r] :@ v) (t'[r] :@ v) _ _ lem1
          apply Typing.app _ (LR.typing lv); apply Typing.rename m j1
          replace h1 := SnRed.rename r h1; simp at h1
          apply SnRed.step_app h1
    all_goals
      apply And.intro; grind
      intro Γ t t' j1 h1 j2 h2
      apply And.intro j1
      apply SnNor.red h1 h2

  theorem LR.var {A x} : Γ ⊢ #x : A -> LR Γ A #x := by
    intro j; apply cr.2.1 j; apply SnNeu.var

  theorem LR.nrec_neutral :
    LR Γ A z ->
    LR Γ (A -t> A) s ->
    Γ ⊢ n : Ty.nat ->
    SnNeu n ->
    LR Γ A (.nrec A z s n)
  := by
    intro h1 h2 h3 h4
    have lem1 := cr.1 h1
    have lem2 := cr.1 h2
    have lem3 := Typing.nrec (LR.typing h1) (LR.typing h2) h3
    apply cr.2.1 lem3
    apply SnNeu.nrec lem1 lem2 h4

  theorem LR.app (flr : LR Γ (A -t> B) f) (alr : LR Γ A a) : LR Γ B (f :@ a) := by
    simp at flr
    have lem := flr.2 TypingRen.id alr; simp at lem
    apply lem

  def LR.nrec (h1 : LR Γ A z) (h2 : LR Γ (A -t> A) s) (j : Γ ⊢ n : Ty.nat)
    : SnNor n -> LR Γ A (.nrec A z s n)
  | .lam t => by cases j
  | .zero =>
    let j' := (Typing.nrec (LR.typing h1) (LR.typing h2) j)
    cr.2.2 j' SnRed.zero h1
  | .succ t =>
    let j' := (Typing.nrec (LR.typing h1) (LR.typing h2) j)
    cr.2.2 j' SnRed.succ (app h2 (nrec h1 h2 (by cases j; grind) t))
  | .neu t => nrec_neutral h1 h2 j t
  | .red r t' =>
    let j' := (Typing.nrec (LR.typing h1) (LR.typing h2) j)
    let r' := SnRed.weaken r
    cr.2.2 j' (SnRed.step_nrec r) (LR.nrec h1 h2 (j.preservation_step r') t')

  theorem fundamental {Γ t A} : Γ ⊢ t : A -> Γ ⊨s t : A := by
    intro j; induction j
    case var Γ T x j =>
      simp; intro σ Δ h
      apply h x T j
    case app Γ A B f a j1 j2 ih1 ih2 =>
      simp; intro σ Δ h; simp at ih1
      replace ih2 := ih2 σ Δ h
      replace ih1 := (ih1 σ Δ h).2 TypingRen.id ih2
      simp at ih1; apply ih1
    case lam Γ A B t j ih =>
      simp; intro σ Δ h; apply And.intro
      apply Typing.lam
      have lem : Γ -[σ]> Δ := GR.forget h
      replace lem : A::Γ -[σ.lift]> A::Δ := TypingSubst.lift A lem
      simp at lem; apply Typing.subst lem j
      intro r Δ' v m lv
      have lem : t[.re 0::σ ∘ r ∘ +1][.su v :: +0] = t[.su v::σ ∘ r.to] := by simp
      apply @cr.2.2 _ _ (t[.su v::σ ∘ r.to])
      apply Typing.app _ (LR.typing lv); apply Typing.lam
      have lem3 := Typing.subst (TypingSubst.lift _ (GR.forget h)) j
      replace lem3 := Typing.rename (TypingRen.lift _ m) lem3
      rw [Ren.to_lift] at lem3; simp at lem3; apply lem3
      have lem2 := @SnRed.beta v A (t[.re 0::σ ∘ r ∘ +1]); simp at lem2
      apply lem2
      apply cr.1 lv
      replace ih := ih (.su v :: σ ∘ r.to) Δ'
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
          have lem := LR.monotone m h; simp at lem
          generalize wdef : r k = w at *
          cases w <;> simp [*]
        case _ t => apply LR.monotone m h
    case zero =>
      intro σ Δ h; simp
      apply And.intro; apply Typing.zero
      apply SnNor.zero
    case succ Γ n j ih =>
      intro σ Δ h; simp
      replace ih := ih σ Δ h; simp at ih
      apply And.intro
      apply Typing.succ ih.1
      apply SnNor.succ ih.2
    case nrec Γ z A s n j1 j2 j3 ih1 ih2 ih3 =>
      intro σ Δ h; simp
      replace ih1 := ih1 σ Δ h
      replace ih2 := ih2 σ Δ h
      replace ih3 := ih3 σ Δ h
      have lem2 := Typing.subst (GR.forget h) j3
      apply LR.nrec ih1 ih2 lem2
      apply cr.1 ih3
end StrongNormalizaton

theorem strong_normalization_inductive {Γ t A} : Γ ⊢ t : A -> SnNor t := by
  intro j
  have lem1 : StrongNormalizaton.GR Γ Γ +0 := by
    simp; intro x T h
    apply StrongNormalizaton.LR.var
    apply Typing.var h
  have lem2 := StrongNormalizaton.fundamental j +0 Γ lem1; simp at lem2
  apply StrongNormalizaton.cr.1 lem2

theorem strong_normalization {Γ t A} : Γ ⊢ t : A -> SN Red t := by
  intro j; apply SnNor.sound
  apply strong_normalization_inductive j
