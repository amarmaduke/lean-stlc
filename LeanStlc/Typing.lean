
import LeanSubst
import LeanStlc.Term

open LeanSubst

@[grind]
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
| zero :
  Typing Γ .zero .nat
| succ :
  Typing Γ n .nat ->
  Typing Γ (.succ n) .nat
| nrec :
  Typing Γ z A ->
  Typing Γ s (A -t> A) ->
  Typing Γ n .nat ->
  Typing Γ (.nrec A z s n) A

notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Typing Γ t A

abbrev TypingRen (r : Ren) (Γ Δ : List Ty) := ∀ {x T}, Γ[x]? = some T -> Δ[r x]? = some T

notation:35 Γ:35 " -⟨" r "⟩> " Δ:35 => TypingRen r Γ Δ

abbrev TypingSubst (σ : Subst Term) (Γ Δ : List Ty) := ∀ {x T}, Γ[x]? = some T -> Δ ⊢ σ x : T

notation:35 Γ:35 " -[" σ "]> " Δ:35 => TypingSubst σ Γ Δ

theorem TypingRen.lift {Γ Δ : List Ty} A {r : Ren} : Γ -⟨r⟩> Δ -> A::Γ -⟨r.lift⟩> A::Δ := by
  intro h x T j
  cases x <;> simp [Ren.lift] at *
  exact j; case _ x =>
  apply h j

theorem TypingRen.comp : X -⟨r1⟩> Y -> Y -⟨r2⟩> Z -> X -⟨r2 ∘ r1⟩> Z := by sorry

infixr:90 " ∘ "  => TypingRen.comp

def Typing.rename (m : Γ -⟨r⟩> Δ) : Γ ⊢ t : A -> Δ ⊢ t[r] : A
| @var Γ T x h => var (m h)
| app f a => app (f.rename m) (a.rename m)
| lam t =>
  let t' := t.rename m.lift
  lam (by rw [Ren.to_lift] at t'; exact t')
| zero => zero
| succ t => succ (t.rename m)
| nrec z s n => nrec (z.rename m) (s.rename m) (n.rename m)

theorem Typing.rename_old {Γ t A} Δ (r : Ren) :
  Γ ⊢ t : A ->
  Γ -⟨r⟩> Δ ->
  Δ ⊢ t[r] : A
:= by
  intro j h
  induction j generalizing Δ r
  case var T x j =>
    replace h := h j
    simp [Ren.to]; apply Typing.var h
  case app j1 j2 ih1 ih2 =>
    apply Typing.app
    replace ih1 := ih1 _ _ h; simp at ih1
    apply ih1
    replace ih2 := ih2 _ _ h; simp at ih2
    apply ih2
  case lam j ih =>
    apply Typing.lam
    replace ih := ih _ _ (TypingRen.lift _ h); simp at ih
    rw [Ren.to_lift] at ih; apply ih
  case _ Γ' =>
    apply Typing.zero
  case _ Γ' n w ih =>
    apply Typing.succ
    apply ih; intro x T w2; apply h; apply w2
  case _ Γ' z A' s n h1 h2 h3 ih1 ih2 ih3 =>
    apply Typing.nrec
    case _ =>
      apply ih1; intro x T j1; apply h; apply j1
    case _ =>
      apply ih2; intro x T j1; apply h; apply j1
    case _ =>
      apply ih3; intro x T j1; apply h; apply j1

theorem TypingSubst.lift {Γ Δ : List Ty} A {σ : Subst Term} : Γ -[σ]> Δ -> A::Γ -[σ.lift]> A::Δ := by
  sorry

-- theorem typing_subst_lift {Γ Δ} A {σ : Subst Term} :
--   (∀ x T, Γ ⊢ #x : T -> Δ ⊢ σ x : T) ->
--   ∀ x T, (A::Γ) ⊢ #x : T -> (A::Δ) ⊢ σ.lift x : T
-- := by
--   intro h x T j
--   cases j; case _ j =>
--   cases x <;> simp at *
--   case _ => subst j; apply Typing.var; simp
--   case _ x =>
--     have h' := h _ _ (Typing.var j)
--     have lem := typing_weaken (A :: Δ) (λ x => x + 1) h' (by {
--       intro x T j2; simp
--       apply Typing.var; simp
--       cases j2; simp [*]
--     }); simp at lem
--     unfold Subst.compose; simp
--     generalize zdef : σ x = z at *
--     cases z <;> simp at *
--     all_goals
--       simp [Term.from_action, Subst.compose] at lem
--       rw [zdef] at lem; simp at lem; apply lem

def Typing.subst (m : Γ -[σ]> Δ) : Γ ⊢ t : A -> Δ ⊢ t[σ] : A
| var h => m h
| app f a => app (f.subst m) (a.subst m)
| lam t => lam (t.subst m.lift)
| zero => zero
| succ t => succ (t.subst m)
| nrec z s n => nrec (z.subst m) (s.subst m) (n.subst m)

theorem Typing.beta : (A::Γ) ⊢ b : B -> Γ ⊢ t : A -> Γ ⊢ b[.su t::+0] : B := by
  intro j1 j2
  apply Typing.subst _ j1
  intro x T h; cases x
  all_goals simp at *; grind
