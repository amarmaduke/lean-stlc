import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Model
import LeanStlc.Typing
import LeanStlc.Preservation

open LeanSubst

namespace StrongNormalizaton3

def Set A := A -> Prop

def Set.empty : Set A := λ _ => False

def ℛ (S : Set Term) : Set Term
| t => ∀ (r:Ren), S t[r]

mutual
  @[grind]
  inductive SnNor : Set Term -> Term -> Prop
  | lam : ℛ S (:λ[A] t) -> SnNor S t -> SnNor S (:λ[A] t)
  | zero : SnNor S .zero
  | succ : SnNor S t -> SnNor S t.succ
  | neu : SnNeu S t -> SnNor S t
  | red : SnRed S t t' -> SnNor S t' -> SnNor S t

  @[grind]
  inductive SnNeu : Set Term -> Term -> Prop
  | var : SnNeu S #x
  | app : SnNeu S s -> SnNor S t -> SnNeu S (s :@ t)
  | nrec : SnNor S z -> SnNor S s -> SnNeu S t -> SnNeu S (.nrec A z s t)

  @[grind]
  inductive SnRed : Set Term -> Term -> Term -> Prop
  | beta : SnNor S t -> SnRed S ((:λ[A] b) :@ t) b[su t::+0]
  | zero : SnNor S s -> SnRed S (.nrec A z s .zero) z
  | succ : SnRed S (.nrec A z s t.succ) (s :@ (.nrec A z s t))
  | step_app : SnRed S s s' -> SnRed S (s :@ t) (s' :@ t)
  | step_nrec : SnRed S n n' -> SnRed S (.nrec A z s n) (.nrec A z s n')
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

def ℰ A := SnNor ⟦ A ⟧

def 𝒞 (Γ : List Ty) (σ : Subst Term) : Prop :=
  ∀ {i T}, Γ[i]? = .some T -> ℰ T (σ i)

@[simp]
def SemanticTyping (Γ : List Ty) (t : Term) (A : Ty) :=
  ∀ σ, 𝒞 Γ σ -> ℰ A t[σ]

local notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Γ t A

theorem lam : ℛ ⟦A -t> B⟧ (:λ[C] b) <-> ∀ (r:Ren) a, ℰ A a -> ℰ B b[su a::r.to] := by
  sorry

theorem ℰ.nrec :
  ℰ A z ->
  ℰ (A -t> A) s ->
  ℰ Ty.nat n ->
  ℰ A (.nrec A z s n)
:= by
  sorry

theorem fundamental : Γ ⊢ t : A -> Γ ⊨ t : A
| .var xj, σ, h =>  h xj
| .app fj aj, σ, h =>
  sorry
| .lam tj, σ, h =>
  let nj' := fundamental tj
  .lam sorry sorry
| .zero, σ, h => .zero
| .succ nj, σ, h =>
  let nj' := fundamental nj σ h
  .succ nj'
| .nrec zj sj nj, σ, h =>
  let zj' := fundamental zj σ h
  let sj' := fundamental sj σ h
  let nj' := fundamental nj σ h
  ℰ.nrec zj' sj' nj'

namespace StrongNormalizaton3
