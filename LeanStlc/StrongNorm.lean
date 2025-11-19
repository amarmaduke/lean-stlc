import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.Progress

open LeanSubst

inductive SnHeadRed : Term -> Term -> Prop where
| beta {t A b} : SN Red t -> SnHeadRed ((:λ[A] b) :@ t) (b[%t :: I])
| app {f f'} a : SnHeadRed f f' -> SnHeadRed (f :@ a) (f' :@ a)

infix:80 " ~>sn " => SnHeadRed

namespace SnHeadRed
  theorem red_compatible {t a b} : t ~>sn a -> t ~> b -> a = b ∨ ∃ z, b ~>sn z ∧ a ~>* z := by
    intro r1 r2
    induction r1 generalizing b
    case _ t' A b' h =>
      cases r2
      case _ => apply Or.inl rfl
      case _ f' r =>
        cases r; case _ b'' r =>
        apply Or.inr; exists (b''[%t' :: I])
        apply And.intro
        apply SnHeadRed.beta h
        apply Star.subst; apply Star.step Star.refl r
      case _ t'' r =>
        apply Or.inr; exists (b'[%t'' :: I])
        apply And.intro
        apply SnHeadRed.beta
        apply SN.preservation_step h r
        apply Red.subst_arg
        intro x; cases x <;> simp
        case _ => apply RedSubstAction.su r
        case _ => apply RedSubstAction.re
    case _ f f' a r1 ih =>
      cases r2
      case _ => cases r1
      case _ f'' r2 =>
        replace ih := ih r2
        cases ih
        case _ ih =>
          subst ih; apply Or.inl rfl
        case _ ih =>
          cases ih; case _ z ih =>
          have lem1 := SnHeadRed.app a ih.1
          apply Or.inr
          exists (z :@ a); apply And.intro lem1
          apply Star.congr2_1 a Term.app Red.app1 ih.2
      case _ a'' r2 =>
        apply Or.inr
        exists (f' :@ a''); apply And.intro
        apply SnHeadRed.app a'' r1
        apply Star.congr2_2 f' Term.app Red.app2
        apply Star.step Star.refl r2
end SnHeadRed

namespace SN

  theorem subterm_app {f a} : SN Red (f :@ a) -> SN Red f ∧ SN Red a := by
    intro h
    generalize zdef : f :@ a = z at *
    induction h generalizing f a
    case _ x h ih =>
    apply And.intro
    case _ =>
      apply SN.sn; intro y r
      subst zdef
      replace ih := ih (y :@ a) (Red.app1 r) rfl
      apply ih.1
    case _ =>
      apply SN.sn; intro y r
      subst zdef
      replace ih := ih (f :@ y) (Red.app2 r) rfl
      apply ih.2

  theorem lam {t A} : SN Red t <-> SN Red (:λ[A] t) := by
    apply Iff.intro
    case _ =>
      intro h; induction h
      case _ t h ih =>
      apply SN.sn; intro y r
      cases r; case _ t' r =>
      apply ih _ r
    case _ =>
      intro h
      generalize zdef : (:λ[A] t) = z at *
      induction h generalizing t
      case _ x h ih =>
      apply SN.sn; intro y r
      subst zdef
      apply ih (:λ[A] y) (Red.lam r) rfl

  theorem neutral_app {f a} : Neutral f -> SN Red f -> SN Red a -> SN Red (f :@ a) := by
    intro h1 h2 h3
    induction h2 generalizing a
    case _ f h2 ih2 =>
      induction h3
      case _ a h3 ih3 =>
      apply SN.sn; intro y r
      cases r
      case _ => cases h1
      case _ f' r =>
        have lem1 := Red.preservation_of_neutral_step h1 r
        have lem2 : SN Red a := SN.sn h3
        apply ih2 f' r lem1 lem2
      case _ a' r =>
        apply ih3 a' r

  theorem weak_head_expansion {t b A} : SN Red t -> SN Red (b[%t::I]) -> SN Red ((:λ[A] b) :@ t) := by
    intro h1; induction h1 generalizing b
    case _ t h1 ih1 =>
    intro h2
    generalize zdef : b[%t :: I] = z at *
    induction h2 generalizing b
    case _ w h2 ih2 =>
    apply SN.sn; intro y r
    cases r
    case _ => rw [zdef]; apply SN.sn h2
    case _ q r =>
      cases r; case _ b' r =>
      have lem : b[%t::I] ~> b'[%t::I] := by
        apply Red.subst (%t::I) r
      apply ih2 (b'[%t::I]) (by rw [<-zdef]; apply lem) rfl
    case _ t' r =>
      have lem1 : SN Red w := SN.sn h2; rw [<-zdef] at lem1
      have lem2 : b[%t::I] ~>* b[%t'::I] := by
        apply Red.subst_arg; intro x
        cases x <;> simp at *
        apply RedSubstAction.su r
        apply RedSubstAction.re
      have lem3 := SN.preservation lem1 lem2
      apply ih1 t' r lem3

  theorem red_app_preservation {f f' a} : f ~>sn f' -> SN Red f -> SN Red a -> SN Red (f' :@ a) -> SN Red (f :@ a) := by
    intro r1 h1 h2 h3
    induction h1 generalizing f' a
    case _ f h1 ih1 =>
    induction h2
    case _ a h2 ih2 =>
    apply SN.sn; intro y r2
    cases r2
    case _ => cases r1
    case _ f'' r =>
      have lem1 := SnHeadRed.red_compatible r1 r
      cases lem1
      case _ lem1 => subst lem1; apply h3
      case _ lem1 =>
        cases lem1; case _ z lem1 =>
        apply ih1 f'' r lem1.1 (SN.sn h2)
        apply SN.preservation h3
        apply Star.congr2_1 a Term.app Red.app1 lem1.2
    case _ a'' r =>
      apply ih2 a'' r
      apply SN.preservation h3
      apply Star.congr2_2 f' Term.app Red.app2 (Star.step Star.refl r)

  theorem backward_closure {t' t} : SN Red t' -> t ~>sn t' -> SN Red t := by
    intro h r; induction r
    case _ h2 => apply weak_head_expansion h2 h
    case _ r ih =>
      have lem := subterm_app h
      apply red_app_preservation r (ih lem.1) lem.2 h

end SN

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
  SNi .red ((:λ[A] b) :@ t, b[%t::I])
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
      have lem := @SNi.beta (t[σ]) A (b[#0::σ ∘ S]) (ih σ h); simp at lem
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
          exists (u[%v::I]); simp
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
        apply @antirename .nor (b[%#x :: I]) (%#x :: I) _ j2
        rfl; unfold IsRen; intro i
        cases i <;> simp
      case step s' j1 =>
        replace ih2 := ih2 s' x rfl
        apply SNi.red j1 ih2

  @[simp]
  abbrev SnPropertyWeakenLemmaType : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, s => Neutral s
  | .nor, _ => True
  | .red, (s, t) => s ~> t

  theorem property_weaken {v i} : SNi v i -> SnPropertyWeakenLemmaType v i := by
    intro h
    induction h <;> simp at *
    case _ => apply Neutral.var
    case _ ih _ => apply Neutral.app ih
    case _ => apply Red.beta
    case _ ih => apply Red.app1 ih

  @[simp]
  abbrev SnSoundLemmaType : (v : SnVariant) -> (i : SnIndices v) -> Prop
  | .neu, s => SN Red s
  | .nor, s => SN Red s
  | .red, (s, t) => s ~>sn t

  theorem sound {v i} : SNi v i -> SnSoundLemmaType v i := by
    intro h; induction h <;> simp at *
    case _ => apply SN.sn; intro y r; cases r
    case _ s t j1 j2 ih1 ih2 =>
      have lem := property_weaken j1; simp at lem
      apply SN.neutral_app lem ih1 ih2
    case _ t A j ih => apply SN.lam.1 ih
    case _ t j ih => apply ih
    case _ ih1 ih2 => apply SN.backward_closure ih2 ih1
    case _ ih => apply SnHeadRed.beta ih
    case _ ih => apply SnHeadRed.app _ ih

  -- TODO: prove completeness
  -- theorem complete {t} : (SN Red t -> SNi .nor t) ∧ (∀ t', t ~>sn t' -> SNi .red (t, t')) := by
  --   induction t
  --   case _ x =>
  --     apply And.intro
  --     intro h; apply SNi.neu (SNi.var)
  --     intro t' h; cases h
  --   case _ f a ih1 ih2 =>
  --     apply And.intro
  --     case _ =>
  --       intro h
  --       have lem1 := sn_subterm_app h
  --       have lem2 := ih1.1 lem1.1
  --       cases lem2
  --       case _ j =>
  --         sorry
  --       case _ h => apply SNi.neu (SNi.app h (ih2.1 lem1.2))
  --       case _ t' j1 j2 =>
  --         have lem : SNi .red (f :@ a, t' :@ a) := by sorry
  --         apply SNi.red lem
  --         sorry
  --     case _ =>
  --       intro t' r; cases r
  --       case _ A b h =>
  --         apply SNi.beta
  --         apply ih2.1 h
  --       case _ f' r =>
  --         apply SNi.step
  --         apply ih1.2 f' r
  --   case _ A t ih =>
  --     apply And.intro
  --     intro h; apply SNi.lam
  --     apply ih.1 (sn_lam.2 h)
  --     intro t' r; cases r
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
      have lem : t[#0::σ ∘ r ∘ S][%v::I] = t[%v::σ ∘ r] := by simp
      apply cr.2.2 _ (t[%v::σ ∘ r])
      have lem2 := @SNi.beta v A (t[#0::σ ∘ r ∘ S]); simp at lem2
      apply lem2
      apply cr.1 _ lv
      replace ih := ih (%v::σ ∘ r)
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

theorem strong_normalization_inductive {Γ t A} : Γ ⊢ t : A -> SNi .nor t := by
  intro j
  have lem1 : StrongNormalizaton.GR Γ I := by
    simp; intro x T h
    apply StrongNormalizaton.var
  have lem2 := StrongNormalizaton.fundamental j I lem1; simp at lem2
  apply StrongNormalizaton.cr.1 _ lem2

theorem strong_normalization {Γ t A} : Γ ⊢ t : A -> SN Red t := by
  intro j; apply @SNi.sound .nor t
  apply strong_normalization_inductive j
