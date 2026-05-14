
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
| inl :
  Typing Γ t A ->
  Typing Γ (.inl t) (.plus A B)
| inr :
  Typing Γ t B ->
  Typing Γ (.inr t) (.plus A B)
| case :
  Typing Γ d (.plus A B) ->
  Typing Γ a (A -t> C) ->
  Typing Γ b (B -t> C) ->
  Typing Γ (.case C d a b) C
| fst :
  Typing Γ t (.product A B) ->
  Typing Γ t.fst A
| snd :
  Typing Γ t (.product A B) ->
  Typing Γ t.snd B
| pair :
  Typing Γ a A ->
  Typing Γ b B ->
  Typing Γ (.pair a b) (.product A B)
| tt :
  Typing Γ .tt .unit
| absurd :
  Typing Γ t .empty ->
  Typing Γ (.absurd A t) A


notation:170 Γ:170 " ⊢ " t:170 " : " A:170 => Typing Γ t A

structure TypingRen (r : Ren) (Γ Δ : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Δ[r x]? = some T

-- def TypingRen (r : Ren) (Γ Δ : List Ty) := ∀ {x T}, Γ[x]? = some T -> Δ[r x]? = some T
notation:35 Γ:35 " -⟨" r "⟩> " Δ:35 => TypingRen r Γ Δ

theorem TypingRen.lift {Γ Δ : List Ty} A {r : Ren} : Γ -⟨r⟩> Δ -> A::Γ -⟨r.lift⟩> A::Δ := by
  intro h; apply mk; intro x T j
  cases x <;> simp [Ren.lift] at *
  exact j; case _ x =>
  apply h.act j

theorem TypingRen.id : X -⟨id⟩> X := by
  apply mk; intro x T h; exact h

theorem TypingRen.succ : X -⟨(· + 1)⟩> A::X := by
  apply mk; intro x T h; exact h

theorem TypingRen.comp : X -⟨r1⟩> Y -> Y -⟨r2⟩> Z -> X -⟨r2 ∘ r1⟩> Z := by
  intro j1 j2; apply mk; intro x T h; simp
  apply j2.act (j1.act h)

infixr:90 " ∘ "  => TypingRen.comp

structure TypingSubst (σ : Subst Term) (Γ Δ : List Ty) where
  act : ∀ {x T}, Γ[x]? = some T -> Δ ⊢ σ x : T

notation:35 Γ:35 " -[" σ "]> " Δ:35 => TypingSubst σ Γ Δ

theorem TypingSubst.succ : X -[+1]> A::X := by
  apply mk
  intro x T h; simp
  apply Typing.var; exact h

def TypingSubst.re (j : Δ[y]? = some A) (m : Γ -[σ]> Δ) : A::Γ -[re y::σ]> Δ :=
  mk (λ {x} {T} h =>
    match x with
    | 0 => .var $ cast (by simp at h; rw [h]) j
    | x + 1 => m.act h)

def TypingSubst.su (j : Δ ⊢ a : A) (m : Γ -[σ]> Δ) : A::Γ -[su a::σ]> Δ :=
  mk (λ {x} {T} h =>
    match x with
    | 0 => cast (by simp; grind) j
    | x + 1 => m.act h)

def TypingSubst.forget (m : X -[r.to]> Y) : X -⟨r⟩> Y :=
  .mk (λ h => match m.act h with | .var h => h)

def TypingRen.to (m : X -⟨r⟩> Y) : X -[r.to]> Y := sorry

def Typing.rename (m : Γ -⟨r⟩> Δ) : Γ ⊢ t : A -> Δ ⊢ t[r] : A
| @var Γ T x h => var (m.act h)
| app f a => app (f.rename m) (a.rename m)
| lam (A := C) t =>
  let t' := t.rename (m.lift C)
  lam (by rw [Ren.to_lift] at t'; exact t')
| zero => zero
| succ t => succ (t.rename m)
| nrec z s n => nrec (z.rename m) (s.rename m) (n.rename m)
| inl t => inl (t.rename m)
| inr t => inr (t.rename m)
| case (A := A) (B := B) h1 h2 h3 => case (h1.rename m) (h2.rename m) (h3.rename m)
| fst t => sorry
| snd t => sorry
| pair a b => sorry
| tt => tt
| absurd h => absurd (h.rename m)


-- theorem Typing.rename_old {Γ t A} Δ (r : Ren) :
--   Γ ⊢ t : A ->
--   Γ -⟨r⟩> Δ ->
--   Δ ⊢ t[r] : A
-- := by
--   intro j h
--   induction j generalizing Δ r
--   case var T x j =>
--     replace h := h j
--     simp [Ren.to]; apply Typing.var h
--   case app j1 j2 ih1 ih2 =>
--     apply Typing.app
--     replace ih1 := ih1 _ _ h; simp at ih1
--     apply ih1
--     replace ih2 := ih2 _ _ h; simp at ih2
--     apply ih2
--   case lam j ih =>
--     apply Typing.lam
--     replace ih := ih _ _ (TypingRen.lift _ h); simp at ih
--     rw [Ren.to_lift] at ih; apply ih
--   case _ Γ' =>
--     apply Typing.zero
--   case _ Γ' n w ih =>
--     apply Typing.succ
--     apply ih; intro x T w2; apply h; apply w2
--   case _ Γ' z A' s n h1 h2 h3 ih1 ih2 ih3 =>
--     apply Typing.nrec
--     case _ =>
--       apply ih1; intro x T j1; apply h; apply j1
--     case _ =>
--       apply ih2; intro x T j1; apply h; apply j1
--     case _ =>
--       apply ih3; intro x T j1; apply h; apply j1

theorem TypingSubst.lift {Γ Δ : List Ty} A {σ : Subst Term} :
  Γ -[σ]> Δ ->
  A::Γ -[σ.lift]> A::Δ
:= by
  intro j; apply TypingSubst.mk
  intro x T h
  cases x <;> simp at *
  case _ => apply Typing.var; simp [h]
  case _ x =>
    have lem := Typing.rename (Δ := A::Δ) TypingRen.succ (j.act h)
    simp at lem; exact lem

theorem variable_switch : Γ[n]? = some T <-> Γ ⊢ #n : T := by
  apply Iff.intro
  case _ =>
    intro h
    apply Typing.var h
  case _ =>
    intro h
    cases h
    case _ j =>
      apply j

theorem TypingSubst.comp : X -[σ]> Y -> Y -⟨r⟩> Z -> X -[σ ∘ r.to]> Z := by
  intro j1 j2; apply mk; intro x T h
  unfold Subst.compose
  replace j1 := j1.act h
  simp
  generalize zdef : σ x = z
  cases z
  case _ n =>
    simp
    rw [zdef] at j1
    have lem := variable_switch.2 j1
    replace j2 := j2.act lem
    apply variable_switch.1
    apply j2
  case _ =>
    simp
    apply Typing.rename; apply j2; rw [zdef] at j1; apply j1

def Typing.subst (m : Γ -[σ]> Δ) : Γ ⊢ t : A -> Δ ⊢ t[σ] : A
| var h => m.act h
| app f a => app (f.subst m) (a.subst m)
| lam (A := C) t => lam (t.subst (m.lift C))
| zero => zero
| succ t => succ (t.subst m)
| nrec z s n => nrec (z.subst m) (s.subst m) (n.subst m)
| inl t => inl (t.subst m)
| inr t => inr (t.subst m)
| case h1 h2 h3 => sorry
| fst t => sorry
| snd t => sorry
| pair a b => sorry
| tt => tt
| absurd h => absurd (h.subst m)

theorem Typing.beta : (A::Γ) ⊢ b : B -> Γ ⊢ t : A -> Γ ⊢ b[.su t::+0] : B := by
  intro j1 j2
  apply Typing.subst _ j1
  apply TypingSubst.mk
  intro x T h; cases x
  all_goals simp at *; grind
