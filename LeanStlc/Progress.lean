import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing

open LeanSubst

namespace Term
  @[simp]
  def is_lam : Term -> Bool
  | .lam _ _ => true
  | _ => false
end Term

inductive Value : Term -> Prop where
| var : Value #x
| app :
  Value f ->
  Value a ->
  ¬ f.is_lam ->
  Value (f :@ a)
| lam :
  Value t ->
  Value (:λ[A] t)

theorem value_sound : Value t -> ∀ t', ¬ (t ~> t') := by
  intro j t' r
  induction j generalizing t'
  case var => cases r
  case app j1 j2 j3 ih1 ih2 =>
    cases r
    case beta => simp at j3
    case app1 r => apply ih1 _ r
    case app2 r => apply ih2 _ r
  case lam j ih =>
    cases r; case _ r =>
    apply ih _ r

inductive VarSpine : Term -> Prop where
| var : VarSpine #x
| app :
  VarSpine h ->
  Value t ->
  VarSpine (h :@ t)

theorem var_spine_not_lam : VarSpine t -> ¬ t.is_lam := by
  intro h1 h2
  induction h1 <;> simp at *

theorem lam_value :
  Γ ⊢ t : (A -t> B) ->
  Value t ->
  (∃ b, (t = :λ[A] b)) ∨ VarSpine t
:= by
  intro j v
  induction v generalizing Γ A B
  case var x =>
    apply Or.inr
    apply VarSpine.var
  case app f a j1 j2 j3 ih1 ih2 =>
    cases j; case _ C j4 j5 =>
    replace ih1 := ih1 j5
    cases ih1
    case _ ih1 =>
      cases ih1; case _ b ih1 =>
      subst ih1; simp at j3
    case _ ih1 =>
      apply Or.inr
      apply VarSpine.app ih1 j2
  case lam t A' v ih =>
    cases j; case _ j =>
    apply Or.inl; apply Exists.intro _; rfl

theorem progress : Γ ⊢ t : A -> Value t ∨ (∃ t', t ~> t') := by
  intro j; induction j
  case var x T j =>
    apply Or.inl; apply Value.var
  case app Γ A B f a j1 j2 ih1 ih2 =>
    cases ih1
    case _ ih1 =>
      cases ih2
      case _ ih2 =>
        have lem := lam_value j1 ih1
        cases lem
        case _ lem =>
          cases lem; case _ b lem =>
          subst lem; apply Or.inr
          exists (b[.su a::I])
          apply Red.beta
        case _ lem =>
          apply Or.inl; apply Value.app ih1 ih2
          apply var_spine_not_lam lem
      case _ ih2 =>
        cases ih2; case _ a' ih2 =>
        apply Or.inr
        exists (f :@ a')
        apply Red.app2 ih2
    case _ ih1 =>
      cases ih1; case _ f' ih1 =>
      apply Or.inr
      exists (f' :@ a)
      apply Red.app1 ih1
  case lam Γ A B t j ih =>
    cases ih
    case _ ih =>
      apply Or.inl
      apply Value.lam ih
    case _ ih =>
      cases ih; case _ t' ih =>
      apply Or.inr
      exists (:λ[A] t')
      apply Red.lam ih
