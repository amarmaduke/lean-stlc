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
  | Γ, Δ, σ => ∀ {x T}, Γ[x]? = .some T -> LR Δ T ↑(σ x)

  @[simp]
  def SemanticTyping Γ t A := ∀ σ Δ, GR Γ Δ σ -> LR Δ A (t[σ])

  notation:170 Γ:170 " ⊨s " t:170 " : " A:170 => SemanticTyping Γ t A

  theorem LR.typing : LR Γ A t -> Γ ⊢ t : A := by
    intro j; induction A generalizing Γ t
    all_goals simp at j; grind

  theorem LR.monotone (m : Γ -⟨r⟩> Δ) : LR Γ A t -> LR Δ A t[r] := by
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
    replace h1 := h1 h2
    apply LR.typing h1

  mutual
    def cr1 : ∀ {A}, LR Γ A t -> SnNor t
    | .base, ⟨j1, j2⟩ => j2
    | .nat, ⟨j1, j2⟩ => j2
    | .arrow A B, ⟨j1, j2⟩ =>
      let j2'  : LR (A::Γ) B (t[+1] :@ #0) := j2 TypingRen.succ $ cr2 (.var $ by simp) .var
      let lem1 : SnNor t[+1]               := SnNor.beta_var (cr1 j2') rfl
      SnNor.antirename (· + 1) lem1 t rfl

    def cr2 : ∀ {A}, Γ ⊢ t : A -> SnNeu t -> LR Γ A t
    | .base, j1, j2 => ⟨j1, .neu j2⟩
    | .nat, j1, j2 => ⟨j1, .neu j2⟩
    | .arrow A B, j, j2 =>
      let lem {r Δ v} (m : Γ -⟨r⟩> Δ) (lv : LR Δ A v) : LR Δ B (t[r.to] :@ v) :=
        let lem1 : Δ ⊢ (t[r] :@ v) : B := .app (j.rename m) lv.typing
        let lem2 : SnNeu (t[r] :@ v)   := .app (j2.rename r) (cr1 lv)
        cr2 lem1 lem2
      ⟨j, lem⟩

    def cr3 : ∀ {A}, Γ ⊢ t : A -> SnRed t t' -> LR Γ A t' -> LR Γ A t
    | .base, j, r, ⟨_, h2⟩ => ⟨j, .red r h2⟩
    | .nat, j, r, ⟨_, h2⟩ => ⟨j, .red r h2⟩
    | .arrow A B, j, sr, tl =>
      let lem {r Δ v} (m : Γ -⟨r⟩> Δ) (lv : LR Δ A v) : LR Δ B (t[r.to] :@ v) :=
        have lem1 : Δ ⊢ (t[r] :@ v) : B            := .app (j.rename m) lv.typing
        have lem2 : SnRed (t[r] :@ v) (t'[r] :@ v) := SnRed.step_app (sr.rename r)
        cr3 lem1 lem2 (tl.2 m lv)
      ⟨j, lem⟩
  end

  theorem LR.var {A x} : Γ ⊢ #x : A -> LR Γ A #x := by
    intro j; apply cr2 j; apply SnNeu.var

  theorem GR.from_ren (m : Γ -⟨r⟩> Δ) : GR Γ Δ r.to
  | _, _, h => LR.var $ .var (m h)

  theorem GR.compose {r : Ren} (a : GR X Y σ) (b : GR Y Z r.to) : GR X Z (σ ∘ r.to)
  | x, T, h =>
    let m : Y -⟨r⟩> Z := TypingSubst.forget b.forget
    cast (by simp) $ LR.monotone m (a h)

  theorem GR.su (j : LR Δ A a) (m : GR Γ Δ σ) : GR (A::Γ) Δ (su a::σ)
  | 0, T, h => cast (by simp; grind) j
  | x + 1, T, h => m h

  theorem LR.nrec_neutral
    (h1 : LR Γ A z)
    (h2 : LR Γ (A -t> A) s)
    (h3 : Γ ⊢ n : Ty.nat)
    (h4 : SnNeu n)
    : LR Γ A (.nrec A z s n)
  :=
    let lem := Typing.nrec (LR.typing h1) (LR.typing h2) h3
    cr2 lem (SnNeu.nrec (cr1 h1) (cr1 h2) h4)

  theorem LR.app (flr : LR Γ (A -t> B) f) (alr : LR Γ A a) : LR Γ B (f :@ a) :=
    cast (by simp) $ flr.2 TypingRen.id alr

  def LR.nrec (h1 : LR Γ A z) (h2 : LR Γ (A -t> A) s) (j : Γ ⊢ n : Ty.nat)
    : SnNor n -> LR Γ A (.nrec A z s n)
  | .lam t => by cases j
  | .zero =>
    let j' := (Typing.nrec (LR.typing h1) (LR.typing h2) j)
    cr3 j' (SnRed.zero (cr1 h2)) h1
  | .succ t =>
    let j' := (Typing.nrec (LR.typing h1) (LR.typing h2) j)
    cr3 j' SnRed.succ (app h2 (nrec h1 h2 (by cases j; grind) t))
  | .neu t => nrec_neutral h1 h2 j t
  | .red r t' =>
    let j' := (Typing.nrec (LR.typing h1) (LR.typing h2) j)
    let r' := SnRed.weaken r
    cr3 j' (SnRed.step_nrec r) (LR.nrec h1 h2 (j.preservation_step r') t')

  def fundamental : Γ ⊢ t : A -> Γ ⊨s t : A
  | .var j, σ, Δ, h => h j
  | .app (f := f) (a := a) fj aj, σ, Δ, h =>
    let aj' := fundamental aj σ Δ h
    let fj' : LR Δ A (f[σ] :@ a[σ]) := cast (by simp) $ (fundamental fj σ Δ h).2 TypingRen.id aj'
    fj'
  | @Typing.lam _ A B t tj, σ, Δ, h =>
    let m1 : Γ -[σ]> Δ := h.forget
    let lem1 := .subst m1 (.lam tj)
    let lem2 {r Δ' v} (m2 : Δ -⟨r⟩> Δ') (lv : LR Δ' A v) : LR Δ' B ((:λ[A] t)[σ][r] :@ v) :=
      let m3  : GR (A :: Γ) Δ' (su v::σ ∘ r.to) := GR.su lv $ h.compose (GR.from_ren m2)
      let tj' : LR Δ' B t[su v::σ ∘ r.to]       := fundamental tj (.su v::σ ∘ r.to) Δ' m3
      let lem2 := @SnRed.beta v A (t[.re 0::σ ∘ r ∘ +1]) (cr1 lv)
      @cr3 _ _ (t[.su v::σ ∘ r.to]) _
        (.app (.rename m2 lem1) (LR.typing lv))
        (cast (by simp) $ lem2)
        tj'
    ⟨lem1, lem2⟩
  | .zero, σ, Δ, h => ⟨.zero, .zero⟩
  | .succ nj, σ, Δ, h =>
    let ⟨ih1, ih2⟩ := fundamental nj σ Δ h
    ⟨ih1.succ, ih2.succ⟩
  | .nrec zj sj nj, σ, Δ, h =>
    let ⟨ih1, ih2⟩ := fundamental nj σ Δ h
    LR.nrec (fundamental zj σ Δ h) (fundamental sj σ Δ h) ih1 ih2
end StrongNormalizaton

theorem strong_normalization_inductive (j : Γ ⊢ t : A) : SnNor t :=
  let lem1 : StrongNormalizaton.GR Γ Γ +0 := by
    simp; intro x T h
    apply StrongNormalizaton.LR.var
    apply Typing.var h
  let lem2 : StrongNormalizaton.LR Γ A t :=
    cast (by simp) $ StrongNormalizaton.fundamental j +0 Γ lem1
  StrongNormalizaton.cr1 lem2

theorem strong_normalization (j : Γ ⊢ t : A) : SN Red t :=
  SnNor.sound $ strong_normalization_inductive j
