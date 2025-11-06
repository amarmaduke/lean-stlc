import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.Preservation

open LeanSubst

def WeakValue : Term -> Bool
| .lam _ _ => true
| _ => false

@[simp]
def VR : Ty -> Term -> Prop
| A -t> B, :λ[_] b => ∀ a, VR A a -> ∃ v, (b[.su a::I]) ~>* v ∧ VR B v
| _, _ => False

@[simp]
def ER : Ty -> Term -> Prop
| A, t => ∃ v, t ~>* v ∧ VR A v

namespace VR
  theorem sound : VR A t -> WeakValue t := by
    intro vr
    induction A generalizing t
    case base => simp at vr
    case arrow A B ih1 ih2 =>
      cases t <;> simp at vr
      case _ b => simp [WeakValue]
end VR

@[simp]
def GR : List Ty -> (Subst Term -> Prop)
| Γ, σ => ∀ x T, Γ[x]? = .some T -> VR T ↑(σ x)

@[simp]
def SemanticTyping Γ t A := ∀ σ, GR Γ σ -> ER A (t[σ])

notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Γ t A

theorem fundamental : Γ ⊢ t : A -> Γ ⊨ t : A := by
  intro j
  induction j
  case var Γ T x h1 =>
    simp; intro σ h2
    replace h2 := h2 x T h1
    generalize zdef : σ x = z at *
    cases z <;> simp at *
    case _ t =>
      exists t
      apply And.intro Star.refl h2
  case app Γ A B f a j1 j2 ih1 ih2 =>
    simp at *
    intro σ h
    replace ih1 := ih1 σ h
    replace ih2 := ih2 σ h
    cases ih1; case _ v1 ih1 =>
    cases ih2; case _ v2 ih2 =>
    cases v1 <;> simp at *
    case _ b =>
    cases ih1; case _ ih1 ih3 =>
    replace ih3 := ih3 v2 ih2.2
    cases ih3; case _ w ih3 =>
    exists w
    apply And.intro _ ih3.2
    apply Star.trans
    apply Star.congr2 Term.app Red.app1 Red.app2 ih1 ih2.1
    apply Star.stepr Red.beta
    apply ih3.1
  case lam Γ A B t j ih =>
    simp; intro σ h
    simp at ih
    exists (:λ[A] t[.re 0 :: σ ∘ S])
    apply And.intro Star.refl; simp
    intro a vr
    have lem := ih (.su a :: σ) (by {
      intro x T h2
      cases x <;> simp at *
      case _ => subst h2; apply vr
      case _ x => apply h x T h2
    }); simp at lem
    apply lem

theorem weak_termination {t A} : [] ⊢ t : A -> ∃ v, t ~>* v ∧ WeakValue v := by
  intro j
  have lem := fundamental j
  simp at lem
  replace lem := lem I; simp at lem
  cases lem; case _ v lem =>
  have weak := VR.sound lem.2
  exists v
  apply And.intro lem.1 weak

theorem consistency_lemma {t} : [] ⊢ t : ⊤ -> WeakValue t -> False := by
  intro h1 h2
  cases t <;> simp [WeakValue] at *
  case lam A b =>
    cases h1

theorem consistency {t} : ¬ ([] ⊢ t : ⊤) := by
  intro h
  have lem := weak_termination h
  cases lem; case _ v lem =>
  have lem2 := preservation h lem.1
  apply consistency_lemma lem2 lem.2
