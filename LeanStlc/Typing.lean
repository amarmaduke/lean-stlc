
import LeanSubst
import LeanStlc.Term

open LeanSubst

inductive Typing : List Ty -> Term -> Ty -> Prop where
| var {Γ T x} :
  Γ[x]? = .some T ->
  Typing Γ #x T
| app {Γ A B f a} :
  Typing Γ f (A -t> B) ->
  Typing Γ a A ->
  Typing Γ (f :@ a) B
| lam {Γ A B t} :
  Typing (A::Γ) t B ->
  Typing Γ (:λ[A] t) (A -t> B)

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Typing Γ t A

theorem typing_renaming_lift {Γ Δ} A {r : Ren} :
  (∀ x T, Γ ⊢ #x : T -> Δ ⊢ #(r x) : T) ->
  ∀ x T, (A::Γ) ⊢ #x : T -> (A::Δ) ⊢ #(r.lift x) : T
:= by
  intro h x T j
  simp [Ren.lift]; cases x <;> simp at *
  case _ =>
    cases j; case _ j =>
    apply Typing.var
    simp at *; subst j; rfl
  case _ x =>
    cases j; case _ j =>
    simp at j; apply Typing.var
    simp; have lem := h x T (Typing.var j)
    cases lem; case _ lem =>
    apply lem

theorem typing_weaken {Γ t A} Δ (r : Ren) :
  Γ ⊢ t : A ->
  (∀ x T, Γ ⊢ #x : T -> Δ ⊢ #(r x) : T) ->
  Δ ⊢ Ren.apply r t : A
:= by
  intro j h
  induction j generalizing Δ r
  case var j =>
    apply h _ _
    apply Typing.var j
  case app j1 j2 ih1 ih2 =>
    apply Typing.app
    replace ih1 := ih1 _ _ h; simp at ih1
    apply ih1
    replace ih2 := ih2 _ _ h; simp at ih2
    apply ih2
  case lam j ih =>
    apply Typing.lam
    replace ih := ih _ _ (typing_renaming_lift _ h); simp at ih
    apply ih

theorem typing_subst_lift {Γ Δ} A {σ : Subst Term} :
  (∀ x T, Γ ⊢ #x : T -> Δ ⊢ σ x : T) ->
  ∀ x T, (A::Γ) ⊢ #x : T -> (A::Δ) ⊢ σ.lift x : T
:= by
  intro h x T j
  cases j; case _ j =>
  cases x <;> simp at *
  case _ => subst j; apply Typing.var; simp
  case _ x =>
    have h' := h _ _ (Typing.var j)
    have lem := typing_weaken (A :: Δ) (λ x => x + 1) h' (by {
      intro x T j2; simp
      apply Typing.var; simp
      cases j2; simp [*]
    }); simp at lem
    unfold Subst.compose; simp
    generalize zdef : σ x = z at *
    cases z <;> simp at *
    apply lem
    rw [SubstMapStable.apply_stable (· + 1) +1 (by rw [Ren.to_succ])] at lem
    apply lem

theorem typing_subst {Γ t A} Δ (σ : Subst Term) :
  Γ ⊢ t : A ->
  (∀ x T, Γ ⊢ #x : T -> Δ ⊢ σ x : T) ->
  Δ ⊢ t[σ] : A
:= by
  intro j h
  induction j generalizing Δ σ
  case var T x j =>
    replace h := h x T; simp
    generalize zdef : σ x = z at *
    cases z <;> simp at *
    all_goals apply h; apply Typing.var j
  case app j1 j2 ih1 ih2 =>
    simp; apply Typing.app
    apply ih1 _ _ h
    apply ih2 _ _ h
  case lam j ih =>
    simp; apply Typing.lam
    replace ih := ih _ _ (typing_subst_lift _ h)
    simp at ih; apply ih

theorem typing_beta {Γ A B b t} : (A::Γ) ⊢ b : B -> Γ ⊢ t : A -> Γ ⊢ b[.su t::+0] : B := by
  intro j1 j2
  apply typing_subst Γ (.su t::+0) j1 (λ x T h => by {
    simp; cases x <;> simp
    case _ =>
      cases h; case _ h =>
      simp at h; subst h
      apply j2
    case _ x =>
      cases h; case _ h =>
      simp at h
      apply Typing.var h
  })
