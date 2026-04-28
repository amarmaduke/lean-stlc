import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.Preservation

open LeanSubst

namespace StrongNormalization4

def CtxSet := List Ty -> Term -> Prop

def CtxSet.empty : CtxSet := λ _ _ => False

def CtxRel := List Ty -> Term -> Term -> Prop

def ℛ (S : CtxSet) : CtxSet
| Γ, t => ∀ {r Δ}, Γ -⟨r⟩> Δ -> S Δ t[r]

mutual
  @[grind]
  inductive SnNor : CtxSet -> CtxSet
  | lam {Γ : List Ty} : ℛ S1 Γ (:λ[A] t) -> SnNor S2 (A::Γ) t -> SnNor S1 Γ (:λ[A] t)
  | zero : SnNor Γ S .zero
  | succ : SnNor Γ S t -> SnNor Γ S t.succ
  | neu : SnNeu Γ S t -> SnNor Γ S t
  | red : SnRed Γ S t t' -> SnNor Γ S t' -> SnNor Γ S t

  @[grind]
  inductive SnNeu : CtxSet -> CtxSet
  | var : SnNeu S Γ #x
  | app : SnNeu S1 Γ s -> SnNor S2 Γ t -> SnNeu S3 Γ (s :@ t)
  | nrec : SnNor S1 Γ z -> SnNor S2 Γ s -> SnNeu S3 Γ t -> SnNeu S4 Γ (.nrec A z s t)

  @[grind]
  inductive SnRed : CtxSet -> CtxRel
  | beta : SnNor S1 Γ t -> SnRed S2 Γ ((:λ[A] b) :@ t) b[su t::+0]
  | zero S1 : SnNor S1 Γ s -> SnRed S2 Γ (.nrec A z s .zero) z
  | succ : SnRed S Γ (.nrec A z s t.succ) (s :@ (.nrec A z s t))
  | step_app : SnRed S1 Γ s s' -> SnRed S2 Γ (s :@ t) (s' :@ t)
  | step_nrec : SnRed S1 Γ n n' -> SnRed S2 Γ (.nrec A z s n) (.nrec A z s n')
end

theorem SnRed.preservation : Γ ⊢ t : A -> SnRed S Γ t t' -> Γ ⊢ t' : A
| Typing.app (Typing.lam j1) j2, SnRed.beta h1 => Typing.beta j1 j2
| Typing.app j1 j2, .step_app h1 => Typing.app (SnRed.preservation j1 h1) j2
| Typing.nrec j1 j2 (Typing.succ j3), .succ => Typing.app j2 (Typing.nrec j1 j2 j3)
| Typing.nrec j1 _ _, .zero S1 h1 => j1
| Typing.nrec j1 j2 j3, .step_nrec h1 => Typing.nrec j1 j2 (SnRed.preservation j3 h1)

mutual
  theorem SnNor.rename (m : Γ -⟨r⟩> Δ) : SnNor S Γ t -> SnNor S Δ t[r]
  | @SnNor.lam S1 A t S2 Γ f th =>
    let th' : SnNor S2 (A :: Δ) t[r.to.lift] := th.rename (m.lift A) |> cast (by rw [<-Ren.to_lift])
    let f' : ℛ S1 Δ (:λ[A] t)[r] := λ {r' ξ} m' => f (.comp m m') |> cast (by simp)
    SnNor.lam f' th'
  | .zero => .zero
  | .succ t => .succ (t.rename m)
  | .neu t => .neu (t.rename m)
  | .red h t' => .red (h.rename m) (t'.rename m)

  theorem SnNeu.rename (m : Γ -⟨r⟩> Δ) : SnNeu S Γ t -> SnNeu S Δ t[r]
  | .var => .var
  | .app s t => .app (s.rename m) (t.rename m)
  | .nrec t z s => .nrec (t.rename m) (z.rename m) (s.rename m)

  theorem SnRed.rename (m : Γ -⟨r⟩> Δ) : SnRed S Γ t t' -> SnRed S Δ t[r] t'[r]
  | @SnRed.beta S1 Γ t S2 A b th => by {
    have lem := @SnRed.beta S1 Δ (t[r]) S2 A (b[.re 0 :: r ∘ +1]) (.rename m th)
    simp at lem; simp; exact lem
  }
  | .zero S1 h => .zero S1 (h.rename m)
  | .succ => .succ
  | .step_app h => .step_app (h.rename m)
  | .step_nrec h => .step_nrec (h.rename m)
end

@[simp]
def 𝒱 : Ty -> CtxSet
| (A -t> B) =>
  λ Γ x => match x with
  | :λ[_] t => ∀ a, Γ ⊢ a : A -> SnNor (𝒱 A) Γ a -> (A :: Γ) ⊢ t : B -> SnNor (𝒱 B) Γ t[su a::+0]
  | _ => False
| _ => CtxSet.empty

def ℰ Γ A := λ t => Γ ⊢ t : A ∧ SnNor (𝒱 A) Γ t

structure SemSubst (Γ : List Ty) (Δ : List Ty) (σ : Subst Term) where
  act : ∀ {i T}, Γ[i]? = .some T -> ℰ Δ T (σ i)

notation:35 Γ:35 " -⟦" σ "⟧> " Δ:35 => SemSubst Γ Δ σ

@[simp]
def SemanticTyping (Γ : List Ty) (t : Term) (A : Ty) :=
  ∀ {σ Δ}, Γ -⟦σ⟧> Δ -> ℰ Δ A t[σ]

local notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Γ t A

theorem SemSubst.forget (m : Γ -⟦σ⟧> Δ) : Γ -[σ]> Δ := .mk λ h => (m.act h).1

theorem SemSubst.lift (m : Γ -⟦σ⟧> Δ) A : A::Γ -⟦σ.lift⟧> A::Δ := sorry

theorem SemSubst.compose (m1 : Γ -⟦σ⟧> Δ) (m2 : Δ -⟨r⟩> ξ) : Γ -⟦σ ∘ r.to⟧> ξ := sorry

theorem SemSubst.su (j : ℰ Δ A a) (m : Γ -⟦σ⟧> Δ) : A::Γ -⟦su a::σ⟧> Δ := sorry

theorem SnNor.appl : ∀ {A B a}, (S = 𝒱 (A -t> B)) -> Γ ⊢ a : (A -t> B) ->  SnNor S Γ a -> ℰ Γ A b -> ℰ Γ B (a :@ b)
| A, B, :λ[_] t, eq, .lam j1, SnNor.lam h1 h2, ⟨j2, j3⟩ =>
  let lem2 : (λ x => x) = @id Nat:= by unfold id; rfl
  let lem : SnNor (𝒱 B) Γ t[su b :: +0] := by
    subst eq; simp [ℛ] at h1
    replace h1 := h1 TypingRen.id b j2 j3 (j1 |> cast (by simp))
    simp at h1; exact h1
  ⟨Typing.app (.lam j1) j2, SnNor.red (SnRed.beta j3) lem⟩
| A, B, a, eq, j1, .neu h1, ⟨j2, j3⟩ => ⟨Typing.app j1 j2, SnNor.neu (SnNeu.app h1 j3)⟩
| A, B, f, eq, j1, .red h1 h2, ⟨j2, j3⟩ => ⟨Typing.app j1 j2, SnNor.red (SnRed.step_app h1) (SnNor.appl eq (SnRed.preservation j1 h1) h2 ⟨j2, j3⟩ ).2⟩

theorem ℰ.nrec :
  ℰ Γ A z ->
  ℰ Γ (A -t> A) s ->
  S = 𝒱 Ty.nat ->
  Γ ⊢ n : Ty.nat ->
  SnNor S Γ n ->
  ℰ Γ A (.nrec A z s n)
| ⟨j1, j2⟩, ⟨j3, j4⟩, _, j5, .zero => ⟨Typing.nrec j1 j3 j5, SnNor.red (SnRed.zero _ j4) j2⟩
| ⟨j1, j2⟩, ⟨j3, j4⟩, eq, Typing.succ j5, .succ h1 => ⟨Typing.nrec j1 j3 (Typing.succ j5) , SnNor.red (SnRed.succ) (SnNor.appl rfl j3 j4 (ℰ.nrec ⟨j1, j2⟩ ⟨j3, j4⟩ eq j5 h1)).2⟩
| ⟨j1, j2⟩, ⟨j3, j4⟩, _, j5, .neu h1 => ⟨Typing.nrec j1 j3 j5, SnNor.neu (SnNeu.nrec j2 j4 h1)⟩
| ⟨j1, j2⟩, ⟨j3, j4⟩, eq, j5, .red h1 h2 => ⟨Typing.nrec j1 j3 j5, SnNor.red (SnRed.step_nrec h1) (ℰ.nrec ⟨j1, j2⟩ ⟨j3,j4⟩ eq (SnRed.preservation j5 h1) h2).2⟩

theorem fundamental : Γ ⊢ t : A -> Γ ⊨ t : A
| .var xj, σ, Δ, h => h.act xj
| .app fj aj, σ, Δ, h =>
  let fj' := fundamental fj h
  let aj' := fundamental aj h
  SnNor.appl rfl fj'.1 fj'.2 aj' |> cast (by simp)
| .lam (A := A') (B := B) (t := t) tj, σ, Δ, h => sorry
| .zero, σ, Δ, h => ⟨Typing.zero, SnNor.zero⟩
| .succ nj, σ, Δ, h =>
  let nj' := fundamental nj h
  ⟨Typing.succ nj'.1, SnNor.succ nj'.2⟩
| .nrec zj sj nj, σ, Δ, h =>
  let zj' := fundamental zj h
  let sj' := fundamental sj h
  let nj' := fundamental nj h
  ℰ.nrec zj' sj' rfl nj'.1 nj'.2

end StrongNormalization4
