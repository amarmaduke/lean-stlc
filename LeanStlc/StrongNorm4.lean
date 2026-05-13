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
  | inl : ℛ S2 Γ t.inl -> SnNor S1 Γ t -> SnNor S2 Γ t.inl
  | inr : ℛ S2 Γ t.inr -> SnNor S1 Γ t -> SnNor S2 Γ t.inr
  | pair : ℛ S3 Γ (.pair a b) -> SnNor S1 Γ a -> SnNor S2 Γ b -> SnNor S3 Γ (.pair a b)
  | tt : SnNor Γ S .tt

  @[grind]
  inductive SnNeu : CtxSet -> CtxSet
  | var : SnNeu S Γ #x
  | app : SnNeu S1 Γ s -> SnNor S2 Γ t -> SnNeu S3 Γ (s :@ t)
  | nrec : SnNor S1 Γ z -> SnNor S2 Γ s -> SnNeu S3 Γ t -> SnNeu S4 Γ (.nrec A z s t)
  | fst : SnNeu S1 Γ t -> SnNeu S2 Γ t.fst
  | snd : SnNeu S1 Γ t -> SnNeu S2 Γ t.snd
  | case : SnNeu S1 Γ d -> SnNor S2 Γ a -> SnNor S3 Γ b -> SnNeu S4 Γ (.case A d a b)

  @[grind]
  inductive SnRed : CtxSet -> CtxRel
  | beta : SnNor S1 Γ t -> SnRed S2 Γ ((:λ[A] b) :@ t) b[su t::+0]
  | zero S1 : SnNor S1 Γ s -> SnRed S2 Γ (.nrec A z s .zero) z
  | succ : SnRed S Γ (.nrec A z s t.succ) (s :@ (.nrec A z s t))
  | step_app : SnRed S1 Γ s s' -> SnRed S2 Γ (s :@ t) (s' :@ t)
  | step_nrec : SnRed S1 Γ n n' -> SnRed S2 Γ (.nrec A z s n) (.nrec A z s n')
  | fst : SnNor S1 Γ b -> SnRed S2 Γ (.fst (.pair a b)) a
  | snd : SnNor S1 Γ a -> SnRed S2 Γ (.snd (.pair a b)) b
  | inl : SnNor S1 Γ b -> SnRed S2 Γ (.case A (.inl t) a b) (a :@ t)
  | inr : SnNor S1 Γ a -> SnRed S2 Γ (.case A (.inr t) a b) (b :@ t)
  | step_case : SnRed S1 Γ d d' -> SnRed S2 Γ (.case A d a b) (.case A d' a b)
  | step_fst : SnRed S1 Γ t t' -> SnRed S2 Γ (t.fst) (t'.fst)
  | step_snd : SnRed S1 Γ t t' -> SnRed S2 Γ (t.snd) (t'.snd)
end

theorem SnRed.preservation : Γ ⊢ t : A -> SnRed S Γ t t' -> Γ ⊢ t' : A
| Typing.app (Typing.lam j1) j2, SnRed.beta h1 => Typing.beta j1 j2
| Typing.app j1 j2, .step_app h1 => Typing.app (SnRed.preservation j1 h1) j2
| Typing.nrec j1 j2 (Typing.succ j3), .succ => Typing.app j2 (Typing.nrec j1 j2 j3)
| Typing.nrec j1 _ _, .zero S1 h1 => j1
| Typing.nrec j1 j2 j3, .step_nrec h1 => Typing.nrec j1 j2 (SnRed.preservation j3 h1)
| Typing.fst (Typing.pair j1 _), fst j3 => j1
| Typing.snd (Typing.pair _ j2), snd j3 => j2
| Typing.case (.inl h1) h2 _, inl h4 => Typing.app h2 h1
| Typing.case (.inr h1) _ h3, inr h5 => Typing.app h3 h1
| Typing.case h1 h2 h3, .step_case h4 => Typing.case (SnRed.preservation h1 h4) h2 h3
| Typing.fst j1, .step_fst h => Typing.fst (SnRed.preservation j1 h)
| Typing.snd j1, .step_snd h => Typing.snd (SnRed.preservation j1 h)
| _, _ => sorry

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
  | .inl h t => .inl (by intro r Δ' h'; sorry) (t.rename m)
  | .inr h t => .inr sorry (t.rename m)
  | .pair h h1 h2 => .pair sorry (h1.rename m) (h2.rename m)
  | .tt => .tt

  theorem SnNeu.rename (m : Γ -⟨r⟩> Δ) : SnNeu S Γ t -> SnNeu S Δ t[r]
  | .var => .var
  | .app s t => .app (s.rename m) (t.rename m)
  | .nrec t z s => .nrec (t.rename m) (z.rename m) (s.rename m)
  | .case (A := A) h1 h2 h3 =>
    .case (h1.rename m) (h2.rename m) (h3.rename m)
  | .snd h => .snd (h.rename m)
  | .fst h => .fst (h.rename m)

  theorem SnRed.rename (m : Γ -⟨r⟩> Δ) : SnRed S Γ t t' -> SnRed S Δ t[r] t'[r]
  | @SnRed.beta S1 Γ t S2 A b th => by {
    have lem := @SnRed.beta S1 Δ (t[r]) S2 A (b[.re 0 :: r ∘ +1]) (.rename m th)
    simp at lem; simp; exact lem
  }
  | .zero S1 h => .zero S1 (h.rename m)
  | .succ => .succ
  | .step_app h => .step_app (h.rename m)
  | .step_nrec h => .step_nrec (h.rename m)
  | .fst h => .fst (h.rename m)
  | .snd h => .snd (h.rename m)
  | .inl h => .inl (h.rename m)
  | .inr h => .inr (h.rename m)
  | .step_case h => .step_case (h.rename m)
  | .step_fst h => .step_fst (h.rename m)
  | .step_snd h => .step_snd (h.rename m)
end

@[simp]
def 𝒱 : Ty -> CtxSet
| (A -t> B) =>
  λ Γ x => match x with
  | :λ[_] t => ∀ a, Γ ⊢ a : A -> SnNor (𝒱 A) Γ a -> (A :: Γ) ⊢ t : B -> SnNor (𝒱 B) Γ t[su a::+0]
  | _ => False
| .plus A B =>
  λ Γ x => match x with
  | .inl t => (Γ ⊢ t : A ∧ SnNor (𝒱 A) Γ t)
  | .inr t => (Γ ⊢ t : B ∧ SnNor (𝒱 B) Γ t)
  | _ => False
| .product A B =>
  λ Γ x => match x with
  | .pair a b => (Γ ⊢ a : A ∧ SnNor (𝒱 A) Γ a) ∧ (Γ ⊢ b : B ∧ SnNor (𝒱 B) Γ b)
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

theorem SemSubst.lift (m : Γ -⟦σ⟧> Δ) A : A::Γ -⟦σ.lift⟧> A::Δ := SemSubst.mk @λ i _ h =>
  ⟨(TypingSubst.lift A (SemSubst.forget m)).act h, match i with
   | 0 => SnNor.neu (SnNeu.var)
   | _ + 1 => by {
      simp_all
      have ⟨e1, e2⟩ := m.act h
      have ren : Δ -⟨(· + 1)⟩> (A :: Δ) := TypingRen.succ
      have lem := SnNor.rename ren e2
      simp at lem
      apply lem
    }⟩

theorem SemSubst.compose (m1 : Γ -⟦σ⟧> Δ) (m2 : Δ -⟨r⟩> ξ) : Γ -⟦σ ∘ r.to⟧> ξ := SemSubst.mk @λ i _ h =>
⟨(TypingSubst.comp (SemSubst.forget m1) (m2)).act h, by {
  have ⟨e1, e2⟩ := m1.act h
  have lem := SnNor.rename m2 e2
  simp at lem
  apply lem
}⟩

theorem SemSubst.su (j : ℰ Δ A a) (m : Γ -⟦σ⟧> Δ) : A::Γ -⟦su a::σ⟧> Δ := SemSubst.mk @λ i _ h =>
⟨(TypingSubst.su j.1 (SemSubst.forget m)).act h, match i with
  | 0 => by simp at *; subst h; apply j.2
  | _ + 1 => by {
      simp_all
      have ⟨e1, e2⟩ := m.act h
      apply e2
    }⟩

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
| ⟨j1, j2⟩, ⟨j3, j4⟩, eq, Typing.succ j5, .succ h1 => ⟨Typing.nrec j1 j3 (Typing.succ j5), SnNor.red (SnRed.succ) (SnNor.appl rfl j3 j4 (ℰ.nrec ⟨j1, j2⟩ ⟨j3, j4⟩ eq j5 h1)).2⟩
| ⟨j1, j2⟩, ⟨j3, j4⟩, _, j5, .neu h1 => ⟨Typing.nrec j1 j3 j5, SnNor.neu (SnNeu.nrec j2 j4 h1)⟩
| ⟨j1, j2⟩, ⟨j3, j4⟩, eq, j5, .red h1 h2 => ⟨Typing.nrec j1 j3 j5, SnNor.red (SnRed.step_nrec h1) (ℰ.nrec ⟨j1, j2⟩ ⟨j3,j4⟩ eq (SnRed.preservation j5 h1) h2).2⟩

theorem ℰ.case:
  S = 𝒱 (.plus A B) ->
  Γ ⊢ d : (.plus A B) ->
  SnNor S Γ d ->
  ℰ Γ (A -t> C) a ->
  ℰ Γ (B -t> C) b ->
  ℰ Γ C (Term.case C d a b)
| eq, Typing.inl j1, SnNor.inl h j2, ⟨j3, j4⟩, ⟨j5, j6⟩ =>
  ⟨Typing.case (Typing.inl j1) j3 j5,
   SnNor.red (SnRed.inl j6) (SnNor.appl rfl j3 j4 ⟨j1, (by subst eq; simp only [ℛ] at h; replace h := @h id Γ TypingRen.id; simp at h; apply h.2)⟩).2⟩
| eq, Typing.inr j1, SnNor.inr h j2, ⟨j3, j4⟩, ⟨j5, j6⟩ =>
  ⟨Typing.case (Typing.inr j1) j3 j5,
   SnNor.red (SnRed.inr j4) (SnNor.appl rfl j5 j6 ⟨j1, (by subst eq; simp only [ℛ] at h; replace h := @h id Γ TypingRen.id; simp at h; apply h.2)⟩).2⟩
| eq, j1, SnNor.neu j2, ⟨j3, j4⟩, ⟨j5, j6⟩ => ⟨Typing.case j1 j3 j5, SnNor.neu (SnNeu.case j2 j4 j6)⟩
| eq, j1, SnNor.red h j2, ⟨j3, j4⟩, ⟨j5, j6⟩ => ⟨Typing.case j1 j3 j5, SnNor.red (SnRed.step_case h) (ℰ.case eq (SnRed.preservation j1 h) j2 ⟨j3, j4⟩ ⟨j5, j6⟩ ).2⟩

theorem ℰ.fst :
  S = 𝒱 (.product A B) ->
  Γ ⊢ t : (.product A B) ->
  SnNor S Γ t ->
  SnNor (𝒱 A) Γ t.fst
| eq, Typing.pair j1 j2, SnNor.pair h h1 h2 => SnNor.red (SnRed.fst h2) (by subst eq;simp only [ℛ] at h; replace h := @h id Γ TypingRen.id; simp at h; apply h.1.2)
| eq, j1, SnNor.neu j2 => SnNor.neu (SnNeu.fst j2)
| eq, j1, SnNor.red h j2 => SnNor.red (SnRed.step_fst h) (ℰ.fst rfl (SnRed.preservation j1 h) (by rw [eq] at j2; apply j2))

theorem ℰ.snd :
  S = 𝒱 (.product A B) ->
  Γ ⊢ t : (.product A B) ->
  SnNor S Γ t ->
  SnNor (𝒱 B) Γ t.snd
| eq, Typing.pair j1 j2, SnNor.pair h h1 h2 => SnNor.red (SnRed.snd h2) (by subst eq;simp only [ℛ] at h; replace h := @h id Γ TypingRen.id; simp at h; apply h.2.2)
| eq, j1, SnNor.neu j2 => SnNor.neu (SnNeu.snd j2)
| eq, j1, SnNor.red h j2 => SnNor.red (SnRed.step_fst h) (ℰ.fst rfl (SnRed.preservation j1 h) (by rw [eq] at j2; apply j2))

theorem fundamental : Γ ⊢ t : A -> Γ ⊨ t : A
| .var xj, σ, Δ, h => h.act xj
| .app fj aj, σ, Δ, h =>
  let fj' := fundamental fj h
  let aj' := fundamental aj h
  SnNor.appl rfl fj'.1 fj'.2 aj' |> cast (by simp)
| .lam (A := A') (B := B) (t := t) tj, σ, Δ, h =>
  let tj' : (A' :: Γ) ⊨ t : B := fundamental tj
  have lem1 {Δ' r}: Δ -⟨r⟩> Δ' → 𝒱 (A' -t> B) Δ' (:λ[A'] t[σ.lift][r.to.lift]) := λ j a w1 w2 w3 =>
    (tj' ((SemSubst.su (And.intro w1 w2)) (SemSubst.compose h j))).2 |> cast (by simp)
  ⟨Typing.subst (SemSubst.forget h) (Typing.lam tj),
   SnNor.lam (S2 := 𝒱 (B)) (t := t[σ.lift]) lem1 (tj' (SemSubst.lift h A')).2⟩
| .zero, σ, Δ, h => ⟨Typing.zero, SnNor.zero⟩
| .succ nj, σ, Δ, h =>
  let nj' := fundamental nj h
  ⟨Typing.succ nj'.1, SnNor.succ nj'.2⟩
| .nrec zj sj nj, σ, Δ, h =>
  let zj' := fundamental zj h
  let sj' := fundamental sj h
  let nj' := fundamental nj h
  ℰ.nrec zj' sj' rfl nj'.1 nj'.2
| .inl (t := t) (A := A) (B := B) nj, σ, Δ, h =>
  let nj' : Γ ⊨ t : A := fundamental nj
  have lem1 {Δ' r} : Δ -⟨r⟩> Δ' -> 𝒱 (.plus A B) Δ' (Term.inl t[σ][r.to]) :=  λ h1 =>
    ⟨(nj' (SemSubst.compose h h1)).1 |> cast (by simp), (nj' (SemSubst.compose h h1)).2 |> cast (by simp)⟩
  ⟨Typing.inl (nj' h).1, SnNor.inl lem1 (nj' h).2⟩
| .inr (t := t) (A := A) (B := B) nj, σ, Δ, h =>
  let nj' : Γ ⊨ t : B := fundamental nj
  have lem1 {Δ' r} : Δ -⟨r⟩> Δ' -> 𝒱 (.plus A B) Δ' (Term.inr t[σ][r.to]) :=  λ h1 =>
  ⟨(nj' (SemSubst.compose h h1)).1 |> cast (by simp), (nj' (SemSubst.compose h h1)).2 |> cast (by simp)⟩
  ⟨Typing.inr (nj' h).1, SnNor.inr lem1 (nj' h).2⟩
| .case (A := A) (B := B) (C := C) h1 h2 h3, σ, Δ, h =>
  let h1' := fundamental h1 h
  let h2' := fundamental h2 h
  let h3' := fundamental h3 h
  (ℰ.case rfl h1'.1 h1'.2 h2' h3')
| .fst nj, σ, Δ, h =>
  let nj' := fundamental nj h
  ⟨Typing.fst nj'.1, (ℰ.fst rfl nj'.1 nj'.2)⟩
| .snd nj, σ, Δ, h =>
  let nj' := fundamental nj h
  ⟨Typing.snd nj'.1, sorry⟩
| .pair h1 h2, σ, Δ, h =>
  let h1' := fundamental h1 h
  let h2' := fundamental h2 h
  ⟨Typing.pair h1'.1 h2'.1, SnNor.pair sorry h1'.2 h2'.2⟩
| .tt, σ, Δ, h => ⟨Typing.tt, SnNor.tt⟩

end StrongNormalization4
