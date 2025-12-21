
import Std.Tactic.Do
import LeanStlc.Typing

namespace Ty
  def decEq : (a b : Ty) -> Decidable (a = b)
  | .base, .base => isTrue rfl
  | .arrow A1 B1, .arrow A2 B2 =>
    match decEq A1 A2, decEq B1 B2 with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isTrue h1, isFalse h2 => isFalse (by {
      intro h; injection h with e1 e2
      apply h2 e2
    })
    | isFalse h1, isTrue h2 => isFalse (by {
      intro h; injection h with e1 e2
      apply h1 e1
    })
    | isFalse h1, isFalse h2 => isFalse (by {
      intro h; injection h with e1 e2
      apply h2 e2
    })
  | .base, .arrow _ _ => isFalse (by intro h; injection h)
  | .arrow _ _, .base => isFalse (by intro h; injection h)
end Ty

instance : Inhabited Ty where
  default := ⊤

instance : DecidableEq Ty := Ty.decEq

@[simp]
def is_arrow : Ty -> Option (Ty × Ty)
| .base => .none
| A -t> B => .some (A, B)

@[simp]
def infer (Γ : List Ty) : Term -> Option Ty
| .var x => Γ[x]?
| f :@ a => do
  let T <- infer Γ f
  let A' <- infer Γ a
  let (A, B) <- is_arrow T
  if A = A' then .some B else .none
| :λ[A] t => do
  let B <- infer (A::Γ) t
  return A -t> B

theorem infer_sound {Γ t A} : infer Γ t = .some A -> Γ ⊢ t : A := by
  intro h
  induction Γ, t using infer.induct generalizing A
  case _ =>
    simp at h
    apply Typing.var h
  case _ ih1 ih2 =>
    simp at h
    replace h := Option.bind_eq_some_iff.1 h
    cases h; case _ T h =>
    cases h; case _ h1 h2 =>
    replace h2 := Option.bind_eq_some_iff.1 h2
    cases h2; case _ A h2 =>
    cases h2; case _ h2 h3 =>
    cases T <;> simp at *
    case _ A' B =>
    cases h3; case _ h3 h4 =>
    subst h3; subst h4
    replace ih1 := ih1 h1
    replace ih2 := ih2 h2
    apply Typing.app ih1 ih2
  case _ ih =>
    simp at h
    replace h := Option.bind_eq_some_iff.1 h
    cases h; case _ T h =>
    cases h; case _ h1 h2 =>
    injection h2 with e; subst e
    apply Typing.lam (ih h1)
