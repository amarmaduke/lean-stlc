import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.Progress

open LeanSubst

inductive SnVariant where
| neu | nor | red

@[simp]
abbrev SnIndices : SnVariant -> Type
| .neu => Term
| .nor => Term
| .red => (Term) × (Term)

inductive SNi : (v : SnVariant) -> SnIndices v -> Prop where
| var {x} : SNi .neu (#x)
| app {s t} :
  SNi .neu s ->
  SNi .nor t ->
  SNi .neu (s :@ t)
| lam {t A} :
  SNi .nor t ->
  SNi .nor (:λ[A] t)
| neu {t} :
  SNi .neu t ->
  SNi .nor t
| red {t t'} :
  SNi .red (t, t') ->
  SNi .nor t' ->
  SNi .nor t
| beta {t A b} :
  SNi .nor t ->
  SNi .red ((:λ[A] b) :@ t, b[.su t :: I])
| step {s s' t} :
  SNi .red (s, s') ->
  SNi .red (s :@ t, s' :@ t)

namespace SNi
  @[simp]
  abbrev SnRenameLemmaType (σ : Subst Term) (_ : IsRen σ) :
    (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, t => SNi .neu (t[σ])
  | .nor, t => SNi .nor (t[σ])
  | .red, (t, t') => SNi .red (t[σ], t'[σ])

  theorem rename {v i} σ h : SNi v i -> SnRenameLemmaType σ h v i := by
    intro j; induction j generalizing σ <;> simp at *
    case var x =>
      unfold IsRen at h
      replace h := h x
      cases h; case _ k h =>
      cases h
      case _ h => rw [h]; simp; apply SNi.var
      case _ h => rw [h]; simp; apply SNi.var
    case app i1 i2 j1 j2 ih1 ih2 =>
      apply SNi.app <;> simp [*]
    case lam t A j ih =>
      apply SNi.lam
      replace ih := ih σ.lift (IsRen.lift h)
      simp at ih; apply ih
    case neu t j ih =>
      apply SNi.neu; simp [*]
    case red t t' j1 j2 ih1 ih2 =>
      apply SNi.red (ih1 _ h) (ih2 _ h)
    case beta t A b j ih =>
      have lem := @SNi.beta (t[σ]) A (b[.re 0 :: σ ∘ S]) (ih σ h); simp at lem
      apply lem
    case step s s' t j ih =>
      apply SNi.step; simp [*]

  @[simp]
  abbrev SnAntiRenameLemmaType (σ : Subst Term) (_ : IsRen σ) :
    (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, t => ∀ z, t = z[σ] -> SNi .neu z
  | .nor, t => ∀ z, t = z[σ] -> SNi .nor z
  | .red, (t, t') =>
    ∀ z, t = z[σ] ->
    ∃ z', t' = z'[σ] ∧ SNi .red (z, z')

  theorem antirename {v i} σ h : SNi v i -> SnAntiRenameLemmaType σ h v i := by
    intro j; induction j generalizing σ <;> simp at *
    case var x =>
      intro z h
      cases z <;> simp at h
      case _ y => apply SNi.var
    case app s t j1 j2 ih1 ih2 =>
      intro z h1; cases z <;> simp at h1
      case _ x =>
        have lem := IsRen.var_apply_forced x h; simp at lem
        cases lem; case _ k lem =>
        rw [lem] at h1; injection h1
      case _ u v =>
        apply SNi.app (ih1 σ h _ h1.1) (ih2 σ h _ h1.2)
    case lam t A j ih =>
      intro z h
      cases z <;> simp at h
      case _ σr x =>
        have lem := IsRen.var_apply_forced x σr; simp at lem
        cases lem; case _ k lem =>
        rw [lem] at h; injection h
      case _ A' b =>
        cases h; case _ h1 h2 =>
        subst h1; apply SNi.lam
        replace ih := ih (σ.lift) (IsRen.lift h) b
        simp at ih; apply ih h2
    case neu t j ih =>
      intro z h2
      replace ih := ih σ h z h2
      apply SNi.neu ih
    case red t t' j1 j2 ih1 ih2 =>
      intro z h2
      have lem := ih1 σ h _ h2
      cases lem; case _ z' h2 =>
      apply SNi.red h2.2
      apply ih2 σ h _ h2.1
    case beta t A b j ih =>
      intro z h2
      cases z <;> simp at h2
      case _ x =>
        have lem := IsRen.var_apply_forced x h; simp at lem
        cases lem; case _ k lem =>
        rw [lem] at h2; injection h2
      case _ u v =>
        cases u <;> simp at h2
        case _ x =>
          have lem := IsRen.var_apply_forced x h; simp at lem
          cases lem; case _ k lem =>
          rw [lem] at h2; injection h2.1
        case _ A' u =>
          cases h2; case _ h1 h2 =>
          cases h1; case _ h1 h3 =>
          subst h1
          replace ih := ih σ h _ h2
          subst h2; subst h3; simp at *
          exists (u[.su v :: I]); simp
          apply SNi.beta ih
    case step s s' t j ih =>
      intro z h2
      cases z <;> simp at h2
      case _ x =>
        have lem := IsRen.var_apply_forced x h; simp at lem
        cases lem; case _ k lem =>
        rw [lem] at h2; injection h2
      case _ u v =>
        replace ih := ih σ h _ h2.1
        cases ih; case _ z' h' =>
        exists (z' :@ v); simp [*]
        apply SNi.step (h'.2)

  @[simp]
  abbrev SnBetaVarLemmaType : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, s => ∀ t x, s = t :@ #x -> SNi .neu t
  | .nor, s => ∀ t x, s = t :@ #x -> SNi .nor t
  | .red, _ => True

  theorem beta_var {v i} : SNi v i -> SnBetaVarLemmaType v i := by
    intro j; induction j <;> simp at *
    case app s t j1 j2 ih1 ih2 =>
      intro u x e1 e2; subst e1; subst e2
      apply j1
    case neu t j ih =>
      intro u x e
      cases t <;> simp at e
      case _ v w =>
      cases e; case _ e1 e2 =>
      subst e1; subst e2
      cases j; case _ j1 j2 =>
      apply SNi.neu j1
    case red t t' j1 j2 ih1 ih2 =>
      intro u x e
      cases t <;> simp at e
      case _ v w =>
      cases e; case _ e1 e2 =>
      subst e1; subst e2
      cases j1
      case beta A b j1 =>
        apply SNi.lam
        apply @antirename .nor (b[.su #x :: I]) (.su #x :: I) _ j2
        rfl; unfold IsRen; intro i
        cases i <;> simp
      case step s' j1 =>
        replace ih2 := ih2 s' x rfl
        apply SNi.red j1 ih2

  -- TODO: prove soundness
  -- @[simp]
  -- abbrev SnSoundLemmaType : (v : SnVariant) -> (i : SnIndices v) -> Prop
  -- | .neu, s => SN Red s
  -- | .nor, s => SN Red s
  -- | .red, (s, t) => SN Red s -> SN Red t

  -- theorem sound {v i} : SNi v i -> SnSoundLemmaType v i := by
  --   intro h; induction h <;> simp at *
  --   case var x =>
  --     apply SN.sn
  --     intro y r
  --     cases r
  --   case app s t j1 j2 ih1 ih2 =>
  --     apply SN.sn
  --     intro y r
  --     sorry
  --   case lam t A j ih =>
  --     sorry
  --   case neu => sorry
  --   case red => sorry
  --   case beta => sorry
  --   case step => sorry

  -- TODO: prove completeness
  -- theorem complete {t} : SN Red t -> SNi .nor t := by sorry

end SNi

namespace StrongNormalizaton
  @[simp]
  def LR : Ty -> (Term -> Prop)
  | .base => λ t => SNi .nor t
  | .arrow A B => λ t => ∀ (σ : Subst Term) (v : Term), IsRen σ -> LR A v -> LR B (t[σ] :@ v)

  @[simp]
  def GR : List Ty -> (Subst Term -> Prop)
  | Γ, σ => ∀ x T, Γ[x]? = .some T -> LR T ↑(σ x)

  @[simp]
  def SemanticTyping Γ t A := ∀ σ, GR Γ σ -> LR A (t[σ])

  notation:170 Γ:170 " ⊨s " t:170 " : " A:170 => SemanticTyping Γ t A

  theorem monotone {A t} (σ : Subst Term) : IsRen σ -> LR A t -> LR A (t[σ]) := by
    intro h1 h2; induction A generalizing t σ
    case _ =>
      simp at *
      apply SNi.rename σ h1 h2
    case _ A B ih1 ih2 =>
      simp at *; intro σ' v σr lv
      replace h2 := h2 (σ ∘ σ') v (IsRen.compose h1 σr) lv
      simp at h2; apply h2

  theorem cr {A} :
    (∀ t, LR A t -> SNi .nor t)
    ∧ (∀ t, SNi .neu t -> LR A t)
    ∧ (∀ t t', SNi .red (t, t') -> LR A t' -> LR A t)
  := by
    induction A <;> simp at *
    case _ =>
      apply And.intro _ _
      apply SNi.neu
      apply SNi.red
    case _ A B ih1 ih2 =>
      apply And.intro
      case _ =>
        intro t h
        apply @SNi.antirename .nor (t[S]) S IsRen.S _ t rfl
        apply @SNi.beta_var .nor _ _ _ 0 rfl
        replace h := h S #0 IsRen.S (ih1.2.1 #0 SNi.var); simp at h
        apply ih2.1 _ h
      case _ =>
        apply And.intro
        case _ =>
          intro t h σ v σr lv
          apply ih2.2.1
          apply SNi.app
          apply SNi.rename σ σr h
          apply ih1.1 _ lv
        case _ =>
          intro t t' h1 h2 σ v σr lr
          have lem1 := h2 σ v σr lr
          apply ih2.2.2 (t[σ] :@ v) (t'[σ] :@ v) _ lem1
          replace h1 := SNi.rename σ σr h1; simp at h1
          apply SNi.step h1

  theorem var {A x} : LR A (#x) := by
    apply cr.2.1; apply SNi.var

  theorem fundamental {Γ t A} : Γ ⊢ t : A -> Γ ⊨s t : A := by
    intro j; induction j
    case var Γ T x j =>
      simp; intro σ h
      replace h := h x T j
      generalize zdef : σ x = z at *
      cases z <;> simp [*]
    case app Γ A B f a j1 j2 ih1 ih2 =>
      simp; intro σ h; simp at ih1
      replace ih1 := ih1 σ h I (a[σ]) IsRen.I
      simp at ih1; apply ih1
      apply ih2 σ h
    case lam Γ A B t j ih =>
      simp; intro σ h r v sr lv
      have lem : t[.re 0::σ ∘ r ∘ S][.su v :: I] = t[.su v::σ ∘ r] := by simp
      apply cr.2.2 _ (t[.su v::σ ∘ r])
      have lem2 := @SNi.beta v A (t[.re 0::σ ∘ r ∘ S]); simp at lem2
      apply lem2
      apply cr.1 _ lv
      replace ih := ih (.su v :: σ ∘ r)
      apply ih
      simp; intro x T j2
      cases x
      case _ =>
        simp; simp at j2; subst j2
        apply lv
      case _ x =>
        simp; simp at j2
        replace h := h x T j2
        unfold Subst.compose; simp
        generalize zdef : σ x = z at *
        cases z <;> simp at *
        case _ k =>
          have lem := monotone r sr h; simp at lem
          generalize wdef : r k = w at *
          cases w <;> simp [*]
        case _ t => apply monotone r sr h
end StrongNormalizaton

theorem strong_normalization {Γ t A} : Γ ⊢ t : A -> SNi .nor t := by
  intro j
  have lem1 : StrongNormalizaton.GR Γ I := by
    simp; intro x T h
    apply StrongNormalizaton.var
  have lem2 := StrongNormalizaton.fundamental j I lem1; simp at lem2
  apply StrongNormalizaton.cr.1 _ lem2
