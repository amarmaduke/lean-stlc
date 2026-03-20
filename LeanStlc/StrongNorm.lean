import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
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
    case base => simp at *; sorry
    case arrow A B ih1 ih2 =>
      apply And.intro
      apply Typing.rename m (typing h)
      intro r' Δ' v m' lv
      replace h := h.2 (m' ∘ m) lv
      simp; exact h
    case nat => sorry


  theorem cr {A} :
    (∀ t, LR Γ A t -> SnNor t)
    ∧ (∀ t, SnNeu t -> LR Γ A t)
    ∧ (∀ t t', SnRed t t' -> LR Γ A t' -> LR Γ A t)
  := by
    sorry
    -- induction A <;> simp at *
    -- case _ =>
    --   apply And.intro _ _
    --   apply SNi.neu
    --   apply SNi.red
    -- case _ A B ih1 ih2 =>
    --   apply And.intro
    --   case _ =>
    --     intro t h
    --     apply @SNi.antirename .nor (t[Ren.to (· + 1)]) (· + 1) _ t rfl
    --     apply @SNi.beta_var .nor _ _ _ 0 rfl
    --     replace h := h (· + 1) (.var 0) (ih1.2.1 (.var 0) SNi.var); simp at h
    --     apply ih2.1 _ h
    --   case _ =>
    --     apply And.intro
    --     case _ =>
    --       intro t h r v lr
    --       apply ih2.2.1
    --       apply SNi.app
    --       apply SNi.rename r h
    --       apply ih1.1 _ lr
    --     case _ =>
    --       intro t t' h1 h2 r v lr
    --       have lem1 := h2 r v lr
    --       apply ih2.2.2 (t[r] :@ v) (t'[r] :@ v) _ lem1
    --       replace h1 := SNi.rename r h1; simp at h1
    --       apply SNi.step h1

  theorem LR.var {A x} : LR Γ A (.var x) := by
    apply cr.2.1; apply SnNeu.var

  theorem LR.nrec_neutral : LR Γ A z -> LR Γ (A -t> A) s -> SnNeu n -> LR Γ A (.nrec A z s n) := by
    intro h1 h2 h3
    replace h1 := cr.1 _ h1
    replace h2 := cr.1 _ h2
    apply cr.2.1
    apply SnNeu.nrec h1 h2 h3

  theorem LR.app (flr : LR Γ (A -t> B) f) (alr : LR Γ A a) : LR Γ B (f :@ a) := by
    sorry

  def LR.nrec (h1 : LR Γ A z) (h2 : LR Γ (A -t> A) s) (j : Γ ⊢ n : Ty.nat) : SnNor n -> LR Γ A (.nrec A z s n)
  | .lam t => by cases j
  | .zero => cr.2.2 _ _ SnRed.zero h1
  | .succ t => cr.2.2 _ _ SnRed.succ (app h2 (nrec h1 h2 (by cases j; grind) t))
  | .neu t => nrec_neutral h1 h2 t
  | .red r t' => cr.2.2 _ _ (SnRed.step_nrec r) (LR.nrec h1 h2 sorry t')

  theorem fundamental {Γ t A} : Γ ⊢ t : A -> Γ ⊨s t : A := by
    intro j; induction j
    case var Γ T x j =>
      simp; intro σ Δ h
      apply h x T j
    case app Γ A B f a j1 j2 ih1 ih2 =>
      simp; intro σ Δ h; simp at ih1
      replace ih1 := (ih1 σ Δ h).2 id (a[σ])
      simp at ih1; apply ih1
      apply ih2 σ Δ h
    case lam Γ A B t j ih =>
      sorry
      -- simp; intro σ Δ h r v lv
      -- have lem : t[.re 0::σ ∘ r ∘ +1][.su v :: +0] = t[.su v::σ ∘ r.to] := by simp
      -- apply cr.2.2 _ (t[.su v::σ ∘ r.to])
      -- have lem2 := @SnRed.beta v A (t[.re 0::σ ∘ r ∘ +1]); simp at lem2
      -- apply lem2
      -- apply cr.1 _ lv
      -- replace ih := ih (.su v :: σ ∘ r.to) Δ
      -- apply ih
      -- simp; intro x T j2
      -- cases x
      -- case _ =>
      --   simp; simp at j2; subst j2
      --   apply lv
      -- case _ x =>
      --   simp; simp at j2
      --   replace h := h x T j2
      --   unfold Subst.compose; simp
      --   generalize zdef : σ x = z at *
      --   cases z <;> simp at *
      --   case _ k =>
      --     have lem := LR.monotone r h; simp at lem
      --     generalize wdef : r k = w at *
      --     cases w <;> simp [*]
      --   case _ t => apply LR.monotone r h
    case zero =>
      intro σ Δ h; simp
      sorry
      -- apply SnNor.zero
    case succ Γ n j ih =>
      intro σ Δ h; simp
      replace ih := ih σ Δ h; simp at ih
      sorry
      -- apply SnNor.succ ih
    case nrec Γ z A s n j1 j2 j3 ih1 ih2 ih3 =>
      intro σ Δ h; simp
      replace ih1 := ih1 σ Δ h
      replace ih2 := ih2 σ Δ h
      replace ih3 := ih3 σ Δ h
      have lem := typing_subst Δ σ j3 (by {
        intro x T j; cases j; case _ j =>
        replace h := h x T j
        apply LR.typing h
      })
      apply LR.nrec ih1 ih2 lem
      apply cr.1 _ ih3
end StrongNormalizaton

theorem strong_normalization_inductive {Γ t A} : Γ ⊢ t : A -> SnNor t := by
  intro j
  have lem1 : StrongNormalizaton.GR Γ Γ +0 := by
    simp; intro x T h
    apply StrongNormalizaton.LR.var
  have lem2 := StrongNormalizaton.fundamental j +0 Γ lem1; simp at lem2
  apply StrongNormalizaton.cr.1 _ lem2

theorem strong_normalization {Γ t A} : Γ ⊢ t : A -> SN Red t := by
  intro j; apply SnNor.sound
  apply strong_normalization_inductive j
