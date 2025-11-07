import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing

open LeanSubst

inductive SnVariant where
| neu | nor | red

@[simp]
abbrev SnIndices : SnVariant -> Type
| .neu => Term
| .nor => Term
| .red => (Term) × (Term)

-- TODO: prove the SN is equivalent to SN Red in LeanSubst
inductive SN : (v : SnVariant) -> SnIndices v -> Prop where
| var {x} : SN .neu (#x)
| app {s t} :
  SN .neu s ->
  SN .nor t ->
  SN .neu (s :@ t)
| lam {t A} :
  SN .nor t ->
  SN .nor (:λ[A] t)
| neu {t} :
  SN .neu t ->
  SN .nor t
| red {t t'} :
  SN .red (t, t') ->
  SN .nor t' ->
  SN .nor t
| beta {t A b} :
  SN .nor t ->
  SN .red ((:λ[A] b) :@ t, b[.su t :: I])
| step {s s' t} :
  SN .red (s, s') ->
  SN .red (s :@ t, s' :@ t)

namespace SN
  -- TODO: generalize renaming lemmas to substituion of 0 size lemmas so we don't
  -- have to mess around with the subst_var_invariant business
  @[simp]
  abbrev SnRenameLemmaType (r : Ren) : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, t => SN .neu (t[r.to])
  | .nor, t => SN .nor (t[r.to])
  | .red, (t, t') => SN .red (t[r.to], t'[r.to])

  theorem rename {v i} r : SN v i -> SnRenameLemmaType r v i := by
    intro j; induction j generalizing r <;> simp at *
    case var x => apply SN.var
    case app i1 i2 j1 j2 ih1 ih2 =>
      apply SN.app <;> simp [*]
    case lam t A j ih =>
      apply SN.lam
      replace ih := ih (Ren.lift r)
      rw [Subst.lift_lemma] at ih; simp at ih
      apply ih
    case neu t j ih =>
      apply SN.neu; simp [*]
    case red t t' j1 j2 ih1 ih2 =>
      apply SN.red (ih1 _) (ih2 _)
    case beta t A b j ih =>
      have lem := @SN.beta (t[r.to]) A (b[.re 0 :: r.to ∘ S]) (ih r); simp at lem
      apply lem
    case step s s' t j ih =>
      apply SN.step; simp [*]

  @[simp]
  abbrev SnAntiRenameLemmaType (r : Ren) : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, t => ∀ z, t = z[r.to] -> SN .neu z
  | .nor, t => ∀ z, t = z[r.to] -> SN .nor z
  | .red, (t, t') =>
    ∀ z, t = z[r.to] ->
    ∃ z', t' = z'[r.to] ∧ SN .red (z, z')

  theorem antirename {v i} r : SN v i -> SnAntiRenameLemmaType r v i := by
    intro j; induction j generalizing r <;> simp at *
    case var x =>
      intro z h
      cases z <;> simp at h
      case _ y => apply SN.var
    case app s t j1 j2 ih1 ih2 =>
      intro z h; cases z <;> simp [Ren.to] at h
      case _ u v =>
      apply SN.app (ih1 r _ h.1) (ih2 r _ h.2)
    case lam t A j ih =>
      intro z h
      cases z <;> simp at h
      case _ => unfold Ren.to at h; simp at h
      case _ A' b =>
        cases h; case _ h1 h2 =>
        subst h1
        apply SN.lam
        replace ih := ih (r.lift) b
        rw [Subst.lift_lemma] at ih; simp at ih
        apply ih h2
    case neu t j ih =>
      intro z h
      apply SN.neu (ih r _ h)
    case red t t' j1 j2 ih1 ih2 =>
      intro z h
      have lem := ih1 r _ h
      cases lem; case _ z' h2 =>
      apply SN.red h2.2
      apply ih2 r _ h2.1
    case beta t A b j ih =>
      intro z h
      cases z <;> simp [Ren.to] at h
      case _ u v =>
      cases u <;> simp [Ren.to] at h
      case _ A' u =>
      cases h; case _ h1 h2 =>
      cases h1; case _ h1 h3 =>
      subst h1
      replace ih := ih r _ h2
      subst h2; subst h3; simp at *
      exists (u[.su v :: I]); simp
      apply SN.beta ih
    case step s s' t j ih =>
      intro z h
      cases z <;> simp [Ren.to] at h
      case _ u v =>
      replace ih := ih r _ h.1
      cases ih; case _ z' h' =>
      exists (z' :@ v); simp [*]
      apply SN.step (h'.2)

  theorem subst_var_invariant_lift_re {σ τ : Subst Term} :
    (∀ i k, σ i = .re k -> τ i = .re k) ->
    (∀ i k, σ.lift i = .re k -> τ.lift i = .re k)
  := by
    intro h1 i k h2
    cases i <;> simp at *; apply h2
    case _ i =>
      unfold Subst.compose at *; simp at *
      generalize zdef : σ i = z at *
      cases z <;> simp at *
      case _ j =>
        subst h2; rw [h1 _ _ zdef]

  theorem subst_var_invariant_lift_su {σ τ : Subst Term} :
    (∀ i t, σ i = .su t -> τ i = .su t ∨ (∃ x, t = #x ∧ τ i = .re x)) ->
    (∀ i t, σ.lift i = .su t -> τ.lift i = .su t ∨ (∃ x, t = #x ∧ τ.lift i = .re x))
  := by
    intro h1 i t h2
    cases i <;> simp at *
    case _ i =>
      unfold Subst.compose at *; simp at *
      generalize zdef : σ i = z at *
      cases z <;> simp at *
      case _ t' =>
        replace h1 := h1 i t' zdef
        cases h1
        case _ h1 =>
          rw [h1]; simp [*]
        case _ h1 =>
          cases h1; case _ w h1 =>
          cases h1; case _ h1 h3 =>
          subst h1; subst h2; rw [h3]; simp

  theorem subst_var_invariant {t} (σ τ : Subst Term) :
    (∀ i k, σ i = .re k -> τ i = .re k) ->
    (∀ i t, σ i = .su t -> τ i = .su t ∨ (∃ x, t = #x ∧ τ i = .re x)) ->
    t[σ] = t[τ]
  := by
    intro h1 h2
    induction t generalizing σ τ <;> simp
    case var x =>
      generalize zdef : σ x = z at *
      cases z <;> simp
      case _ k => rw [h1 x k zdef]
      case _ t =>
        have lem := h2 x t zdef
        cases lem
        case _ lem => rw [lem]
        case _ lem =>
          cases lem; case _ w lem =>
          cases lem; case _ e lem =>
          subst e; rw [lem]
    case app f a ih1 ih2 =>
      apply And.intro (ih1 _ _ h1 h2) (ih2 _ _ h1 h2)
    case lam A t ih =>
      replace ih := ih σ.lift τ.lift
        (subst_var_invariant_lift_re h1)
        (subst_var_invariant_lift_su h2)
      simp at ih; apply ih

  @[simp]
  abbrev SnBetaVarLemmaType : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, s => ∀ t x, s = t :@ #x -> SN .neu t
  | .nor, s => ∀ t x, s = t :@ #x -> SN .nor t
  | .red, _ => True

  theorem beta_var {v i} : SN v i -> SnBetaVarLemmaType v i := by
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
      apply SN.neu j1
    case red t t' j1 j2 ih1 ih2 =>
      intro u x e
      cases t <;> simp at e
      case _ v w =>
      cases e; case _ e1 e2 =>
      subst e1; subst e2
      cases j1
      case beta A b j1 =>
        apply SN.lam
        rw [subst_var_invariant (.su #x :: I) (.re x :: I)] at j2
        apply @antirename .nor (b[.re x :: I]) (x :: id) j2
        have lem : .re x :: I = @Ren.to Term (x :: id) := by
          funext; case _ x =>
          cases x <;> simp [Ren.to]
        rw [lem]
        case _ =>
          intro i k h
          cases i <;> simp at *
          apply h
        case _ =>
          intro i t h
          cases i <;> simp at *
          subst h; rfl
      case step s' j1 =>
        replace ih2 := ih2 s' x rfl
        apply SN.red j1 ih2

end SN

namespace StrongNormalizaton
  @[simp]
  def LR : Ty -> (Term -> Prop)
  | .base => λ t => SN .nor t
  | .arrow A B => λ t => ∀ (r : Ren) (v : Term), LR A v -> LR B (t[r.to] :@ v)

  @[simp]
  def GR : List Ty -> (Subst Term -> Prop)
  | Γ, σ => ∀ x T, Γ[x]? = .some T -> LR T ↑(σ x)

  @[simp]
  def SemanticTyping Γ t A := ∀ σ, GR Γ σ -> LR A (t[σ])

  notation:170 Γ:170 " ⊨s " t:170 " : " A:170 => SemanticTyping Γ t A

  theorem monotone {A t} (r : Ren) : LR A t -> LR A (t[r.to]) := by
    intro h; induction A generalizing t r
    case _ =>
      simp at *
      apply SN.rename _ h
    case _ A B ih1 ih2 =>
      simp at *; intro r' v lv
      replace h := h (r' ∘ r) v lv
      simp at h; apply h

  theorem cr {A} :
    (∀ t, LR A t -> SN .nor t)
    ∧ (∀ t, SN .neu t -> LR A t)
    ∧ (∀ t t', SN .red (t, t') -> LR A t' -> LR A t)
  := by
    induction A <;> simp at *
    case _ =>
      apply And.intro _ _
      apply SN.neu
      apply SN.red
    case _ A B ih1 ih2 =>
      apply And.intro
      case _ =>
        intro t h
        apply @SN.antirename .nor (t[S]) (λ x => x + 1) _ t rfl
        apply @SN.beta_var .nor _ _ _ 0 rfl
        replace h := h (λ x => x + 1) #0 (ih1.2.1 #0 SN.var); simp at h
        apply ih2.1 _ h
      case _ =>
        apply And.intro
        case _ =>
          intro t h r v lv
          apply ih2.2.1
          apply SN.app
          apply SN.rename r h
          apply ih1.1 _ lv
        case _ =>
          intro t t' h1 h2 r v lr
          have lem1 := h2 r v lr
          apply ih2.2.2 (t[r.to] :@ v) (t'[r.to] :@ v) _ lem1
          replace h1 := SN.rename r h1; simp at h1
          apply SN.step h1

  theorem var {A x} : LR A (#x) := by
    apply cr.2.1; apply SN.var

  theorem fundamental {Γ t A} : Γ ⊢ t : A -> Γ ⊨s t : A := by
    intro j; induction j
    case var Γ T x j =>
      simp; intro σ h
      replace h := h x T j
      generalize zdef : σ x = z at *
      cases z <;> simp [*]
    case app Γ A B f a j1 j2 ih1 ih2 =>
      simp; intro σ h; simp at ih1
      replace ih1 := ih1 σ h (λ x => x) (a[σ])
      simp at ih1; apply ih1
      apply ih2 σ h
    case lam Γ A B t j ih =>
      simp; intro σ h r v lv
      have lem : t[.re 0::σ ∘ r.to ∘ S][.su v :: I] = t[.su v::σ ∘ r.to] := by simp
      apply cr.2.2 _ (t[.su v::σ ∘ r.to])
      have lem2 := @SN.beta v A (t[.re 0::σ ∘ r.to ∘ S]); simp at lem2
      apply lem2
      apply cr.1 _ lv
      replace ih := ih (.su v :: σ ∘ r.to)
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
          have lem := monotone r h; simp at lem
          apply lem
        case _ t => apply monotone r h
end StrongNormalizaton

theorem strong_normalization {Γ t A} : Γ ⊢ t : A -> SN .nor t := by
  intro j
  have lem1 : StrongNormalizaton.GR Γ I := by
    simp; intro x T h
    apply StrongNormalizaton.var
  have lem2 := StrongNormalizaton.fundamental j I lem1; simp at lem2
  apply StrongNormalizaton.cr.1 _ lem2
