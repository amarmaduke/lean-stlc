import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing

open LeanSubst

theorem preservation_step {Γ A t t'} : Γ ⊢ t : A -> t ~> t' -> Γ ⊢ t' : A := by
  intro j r
  induction j generalizing t'
  case var => cases r
  case app j1 j2 ih1 ih2 =>
    cases r
    case beta =>
      cases j1; case _ j1 =>
      apply typing_beta j1 j2
    case app1 r =>
      replace ih1 := ih1 r
      apply Typing.app ih1 j2
    case app2 r =>
      replace ih2 := ih2 r
      apply Typing.app j1 ih2
  case lam j ih =>
    cases r
    case lam r =>
      replace ih := ih r
      apply Typing.lam ih

theorem preservation {Γ A t t'} : Γ ⊢ t : A -> t ~>* t' -> Γ ⊢ t' : A := by
  intro j r
  induction r
  case _ => apply j
  case _ r1 r2 ih => apply preservation_step ih r2
