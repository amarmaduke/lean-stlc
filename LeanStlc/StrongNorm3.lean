import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Model
import LeanStlc.Typing
import LeanStlc.Preservation

open LeanSubst

namespace StrongNormalization3

def Set A := A -> Prop

def Set.empty : Set A := λ _ => False

def ℛ (S : Set Term) : Set Term
| t => ∀ (r:Ren), S t[r]

mutual
  @[grind]
  inductive SnNor : Set Term -> Term -> Prop
  | lam : S1 (:λ[A] t) -> SnNor S2 t -> SnNor S1 (:λ[A] t) -- I got rid of the ℛ
  | zero : SnNor S .zero
  | succ : SnNor S t -> SnNor S t.succ
  | neu : SnNeu S t -> SnNor S t
  | red : SnRed S t t' -> SnNor S t' -> SnNor S t

  @[grind]
  inductive SnNeu : Set Term -> Term -> Prop
  | var : SnNeu S #x
  | app : SnNeu S1 s -> SnNor S2 t -> SnNeu S3 (s :@ t)
  | nrec : SnNor S1 z -> SnNor S2 s -> SnNeu S3 t -> SnNeu S4 (.nrec A z s t)

  @[grind]
  inductive SnRed : Set Term -> Term -> Term -> Prop
  | beta : SnNor S1 t -> SnRed S2 ((:λ[A] b) :@ t) b[su t::+0]
  | zero S1 : SnNor S1 s -> SnRed S2 (.nrec A z s .zero) z
  | succ : SnRed S (.nrec A z s t.succ) (s :@ (.nrec A z s t))
  | step_app : SnRed S1 s s' -> SnRed S2 (s :@ t) (s' :@ t)
  | step_nrec : SnRed S1 n n' -> SnRed S2 (.nrec A z s n) (.nrec A z s n')
end

@[simp]
abbrev 𝒜 (A B : Set Term) : Set Term := λ t => ∀ a, SnNor A a -> SnNor B t[su a::+0]

@[simp]
instance : Model $ Set Term where
  A A B := fun
    | .lam _ t => 𝒜 A B t
    | _ => False
  P := Set.empty
  N := Set.empty

@[simp]
def 𝒱 (Γ : List Ty) : Ty -> Set Term
| (A -t> B) =>
  λ x => match x with
  | :λ[_] t => ∀ a, Γ ⊢ a : A -> SnNor (𝒱 Γ A) a -> (A :: Γ) ⊢ t : B -> SnNor (𝒱 Γ B) t[su a::+0]
  | _ => False
| _ => Set.empty

def ℰ Γ A := λ t => Γ ⊢ t : A ∧ SnNor (𝒱 Γ A) t

def 𝒞 (Γ : List Ty) (Δ : List Ty) (σ : Subst Term) : Prop :=
  ∀ {i T}, Γ[i]? = .some T -> ℰ Δ T (σ i)

@[simp]
def SemanticTyping (Γ : List Ty) (t : Term) (A : Ty) :=
  ∀ σ Δ, 𝒞 Γ Δ σ -> ℰ Δ A t[σ]

local notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Γ t A

theorem SnRed.preservation : Γ ⊢ t : A -> SnRed S t t' -> Γ ⊢ t' : A
| Typing.app (Typing.lam j1) j2, SnRed.beta h1 => Typing.beta j1 j2
| Typing.app j1 j2, .step_app h1 => Typing.app (SnRed.preservation j1 h1) j2
| Typing.nrec j1 j2 (Typing.succ j3), .succ => Typing.app j2 (Typing.nrec j1 j2 j3)
| Typing.nrec j1 _ _, .zero S1 h1 => j1
| Typing.nrec j1 j2 j3, .step_nrec h1 => Typing.nrec j1 j2 (SnRed.preservation j3 h1)

-- theorem lam1 : ℛ ⟦A -t> B⟧ (:λ[C] b) -> Γ ⊢ (:λ[C] b) : (A -t> B) -> ∀ (r:Ren) a, Γ -⟨r⟩> Δ -> ℰ Δ A a -> ℰ Δ B b[su a::r.to]
-- | h1, h3, r, a, h2, h4 =>
--   by
--     simp only [ℛ] at h1; replace h1 := h1 r; simp at h1;
--     apply And.intro _
--     apply h1; exact h4.2
--     cases h3
--     case _ h3 =>
--       replace h2 : Γ -[r.to]> Δ := h2.to
--       replace h2 : (A :: Γ) -[su a :: r.to]> Δ := TypingSubst.su h4.1 h2
--       apply Typing.subst h2 h3

-- theorem lam2 : (∀ (r:Ren) a, Γ -⟨r⟩> Δ -> ℰ Δ A a -> ℰ Δ B b[su a::r.to]) -> (ℛ ⟦A -t> B⟧ (:λ[C] b) ∧ Γ ⊢ (:λ[C] b) : (A -t> B)) := by
--   intro h
--   apply And.intro
--   intro r
--   simp

theorem SnNor.appl : ∀ {A B a}, (S = 𝒱 Γ (A -t> B)) -> Γ ⊢ a : (A -t> B) ->  SnNor S a -> ℰ Γ A b -> ℰ Γ B (a :@ b)
| A, B, :λ[_] t, eq, .lam j1, SnNor.lam h1 h2, ⟨j2, j3⟩ =>
  let lem2 : (λ x => x) = @id Nat:= by unfold id; rfl
  let lem : SnNor (𝒱 Γ B) t[su b :: +0] := by
    --simp only [ℛ] at h1
    subst eq
    simp only [𝒱] at h1
    simp at h1
    apply h1; apply j2; apply j3; apply j1
  ⟨Typing.app (.lam j1) j2, SnNor.red (SnRed.beta j3) lem⟩
| A, B, a, eq, j1, .neu h1, ⟨j2, j3⟩ => ⟨Typing.app j1 j2, SnNor.neu (SnNeu.app h1 j3)⟩
| A, B, f, eq, j1, .red h1 h2, ⟨j2, j3⟩ => ⟨Typing.app j1 j2, SnNor.red (SnRed.step_app h1) (SnNor.appl eq (SnRed.preservation j1 h1) h2 ⟨j2, j3⟩ ).2⟩

theorem ℰ.nrec :
  ℰ Γ A z ->
  ℰ Γ (A -t> A) s ->
  S = ⟦ Ty.nat ⟧ ->
  Γ ⊢ n : Ty.nat ->
  SnNor S n ->
  ℰ Γ A (.nrec A z s n)
| ⟨j1, j2⟩, ⟨j3, j4⟩, _, j5, .zero => ⟨Typing.nrec j1 j3 j5, SnNor.red (SnRed.zero _ j4) j2⟩
| ⟨j1, j2⟩, ⟨j3, j4⟩, eq, Typing.succ j5, .succ h1 => ⟨Typing.nrec j1 j3 (Typing.succ j5) , SnNor.red (SnRed.succ) (SnNor.appl rfl j3 j4 (ℰ.nrec ⟨j1, j2⟩ ⟨j3, j4⟩ eq j5 h1)).2⟩
| ⟨j1, j2⟩, ⟨j3, j4⟩, _, j5, .neu h1 => ⟨Typing.nrec j1 j3 j5, SnNor.neu (SnNeu.nrec j2 j4 h1)⟩
| ⟨j1, j2⟩, ⟨j3, j4⟩, eq, j5, .red h1 h2 => ⟨Typing.nrec j1 j3 j5, SnNor.red (SnRed.step_nrec h1) (ℰ.nrec ⟨j1, j2⟩ ⟨j3,j4⟩ eq (SnRed.preservation j5 h1) h2).2⟩

theorem context_renaming : 𝒞 Γ Δ σ -> Γ ⊢ t : A -> Δ ⊢ t[σ] : A
| h1, h2 =>
  let lem : ∀ {i : Nat} {T : Ty}, Γ[i]? = some T → Δ ⊢ ↑(σ i) : T := by
    intro i T j1
    have h1 := h1 j1
    simp only [ℰ] at h1
    rcases h1 with ⟨e1, e2⟩
    exact e1
  Typing.subst lem h2

theorem context_to_typingsubst : 𝒞 Γ Δ σ -> (∀ {x T}, Γ[x]? = some T -> Δ ⊢ σ x : T)
| h1, _, _, h2 => (h1 h2).1

mutual
  theorem SnNor.lift {σ : Subst Term} :
    SnNor (𝒱 Δ T) (σ n) ->
    SnNor (𝒱 (A :: Δ) T) (σ.lift (n + 1))
  := by
    intro h1
    generalize zdef : (σ n) = z
    rw [zdef] at h1
    cases z
    case _ =>
      cases n
      case _ =>
        unfold Subst.lift
        simp
        rw [zdef]
        simp
        apply SnNor.neu
        apply SnNeu.var
      case _ =>
        unfold Subst.lift
        simp
        rw [zdef]
        simp
        apply SnNor.neu
        apply SnNeu.var
    case _ t =>
      cases h1
      case _ S2 t A' h1 h2 =>
        unfold Subst.lift
        simp
        rw [zdef]
        simp
        sorry
      case _ =>
        sorry
      case _ =>
        sorry
      case _ =>
        sorry
      case _ =>
        sorry

  theorem SnNeu.lift {σ : Subst Term} :
    SnNeu (𝒱 Δ T) (σ n) ->
    SnNeu (𝒱 (A :: Δ) T) (σ.lift (n + 1))
  := by
    sorry
end

theorem context_lift : 𝒞 Γ Δ σ -> 𝒞 (A :: Γ) (A :: Δ) σ.lift
| h1, 0, _, h4 => ⟨TypingSubst.lift (Γ := Γ) (Δ := Δ) (σ := σ) A (λ x => (h1 x).1) h4, (SnNor.neu (SnNeu.var))⟩
| h1, _ + 1, _, h4 => ⟨TypingSubst.lift (Γ := Γ) (Δ := Δ) (σ := σ) A (λ x => (h1 x).1) h4, SnNor.lift (h1 h4).2⟩

-- mutual
--   def SnNor.rename (r : Ren) : SnNor S t -> SnNor S t[r]
--   | @SnNor.lam S1 S2 t A f th =>
--     let lem : SnNor S2 t[r.to.lift] := by
--       rw [<-Ren.to_lift]
--       exact .rename r.lift th
--     let lem2 : S1 (:λ[A] t[r.to.lift]) := by
--       --rw [<-Ren.to_lift]
--       simp only [ℛ] at *
--       intro r'
--       simp at *
--       apply f
--     SnNor.lam lem2 lem
--   | .zero => .zero
--   | .succ t => .succ (t.rename r)
--   | .neu t => .neu (t.rename r)
--   | .red h t' => .red (h.rename r) (t'.rename r)

--   def SnNeu.rename (r : Ren) : SnNeu S t -> SnNeu S t[r]
--   | .var => .var
--   | .app s t => .app (s.rename r) (t.rename r)
--   | .nrec t z s => .nrec (t.rename r) (z.rename r) (s.rename r)

--   def SnRed.rename (r : Ren) : SnRed S t t' -> SnRed S t[r] t'[r]
--   | @SnRed.beta S1 t S2 A b th => by {
--     have lem := @SnRed.beta S1 (t[r]) S2 A (b[.re 0 :: r ∘ +1]) (.rename r th)
--     simp at lem; simp; exact lem
--   }
--   | .zero S1 h => .zero S1 (h.rename r)
--   | .succ => .succ
--   | .step_app h => .step_app (h.rename r)
--   | .step_nrec h => .step_nrec (h.rename r)
-- end

@[simp]
theorem test : Term.smap σ t = t[σ] := by
  induction t
  case _ =>
    simp
  case _ ih1 ih2 =>
    simp
    apply And.intro
    apply ih1
    apply ih2
  case _ A t ih =>
    simp
    unfold Term.smap
    sorry
  case _ =>
    simp
  case _ ih =>
    simp
    apply ih
  case _ ih1 ih2 ih3 =>
    simp
    apply And.intro; apply ih1; apply And.intro; apply ih2; apply ih3

theorem fundamental : Γ ⊢ t : A -> Γ ⊨ t : A
| .var xj, σ, Δ, h =>  h xj
| .app fj aj, σ, Δ, h =>
  let fj' := (fundamental fj) σ Δ
  let aj' := (fundamental aj) σ Δ
  by simp; apply SnNor.appl rfl (by apply context_renaming h fj) (fj' h).2 (aj' h)
| .lam (A := A') (B := B) (t := t) tj, σ, Δ, h =>
  let nj' := fundamental tj
  let lem : (𝒱 Δ (A' -t> B)) (:λ[A'] t[σ.lift]) := by
    intro a j1 j2 j3
    simp at *
    let lem2 : 𝒞 (A' :: Γ) Δ (su a :: σ) := by
      unfold 𝒞 at *
      intro i T w
      unfold ℰ at *
      apply And.intro
      case _ =>
        cases i
        case _ =>
          simp
          simp at w
          subst w
          apply j1
        case _ n =>
          let lem3 : σ n = (su a :: σ) (n + 1) := by simp
          let lem4 : Γ[n]? = (A' :: Γ)[n + 1]? := by simp
          replace h :=@ h n T
          rw [lem4] at h
          rw [lem3] at h
          replace h := h w
          apply h.1
      case _ =>
        cases i
        case _ =>
          simp
          simp at w
          subst w
          apply j2
        case _ n =>
          replace h := @h n T
          let lem3 : σ n = (su a :: σ) (n + 1) := by simp
          let lem4 : Γ[n]? = (A' :: Γ)[n + 1]? := by simp
          rw [lem4] at h
          rw [lem3] at h
          replace h := h w
          apply h.2
    replace nj' := nj' (su a :: σ) Δ lem2
    apply nj'.2
  ⟨context_renaming h (Typing.lam tj),
   SnNor.lam (S2 := (𝒱 (A'::Δ) B)) lem (nj' _ (A'::Δ) (context_lift h)).2⟩
  -- let jj := TypingSubst.lift (Γ := Γ) (Δ := Δ) (σ := σ) (A := A')
  -- have lem : ∀ {x T}, Γ[x]? = some T -> Δ ⊢ σ x :T := by
  --   intro x T h2
  --   simp only [𝒞] at h
  --   replace h := @h x T h2
  --   simp only [ℰ] at h
  --   rcases h with ⟨e1,e2⟩
  --   apply e1
  -- have lem2 : 𝒞 (A' :: Γ) (A' :: Δ) σ.lift := by
  --   apply context_lift
  --   apply h
  -- have lem3 : ∀ a (r : Ren), 𝒞 (A' :: Γ) (Δ) (su a :: σ ∘ r.to) := by
  --   intro a r
  --   apply context_shift
  --   apply h
  -- ⟨Typing.lam (context_renaming
  -- (by intro i T h2; simp only [ℰ]; unfold TypingSubst at *; simp only [𝒞, ℰ] at lem2; replace lem2 := @lem2 i T h2; exact lem2) tj), SnNor.lam (S2 := ⟦ B ⟧)
  -- (by sorry)
  -- (by simp at nj'; simp only [ℰ] at nj'; unfold TypingSubst at *; replace nj' := nj' σ.lift (A'::Δ) lem2; rcases nj' with ⟨e1,e2⟩; exact e2)⟩
| .zero, σ, Δ, h => ⟨Typing.zero, SnNor.zero⟩
| .succ nj, σ, Δ, h =>
  let nj' := fundamental nj σ Δ h
  ⟨Typing.succ nj'.1, SnNor.succ nj'.2⟩
| .nrec zj sj nj, σ, Δ, h =>
  let zj' := fundamental zj σ Δ h
  let sj' := fundamental sj σ Δ h
  let nj' := fundamental nj σ Δ h
  ℰ.nrec zj' sj' rfl nj'.1 nj'.2

namespace StrongNormalization3
