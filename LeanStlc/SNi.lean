import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.Progress

open LeanSubst

inductive SnHeadRed : Term -> Term -> Prop where
| beta {t A b} : SN Red t -> SnHeadRed ((:λ[A] b) :@ t) (b[.su t::+0])
| zero : SnHeadRed (.nrec A z s .zero) z
| succ : SnHeadRed (.nrec A z s (.succ n)) (s :@ (.nrec A z s n))
| nrec : SnHeadRed n n' -> SnHeadRed (.nrec A z s n) (.nrec A z s n')
| app {f f'} a : SnHeadRed f f' -> SnHeadRed (f :@ a) (f' :@ a)

infix:80 " ~>sn " => SnHeadRed

namespace SnHeadRed
  theorem red_compatible {t a b} : t ~>sn a -> t ~> b -> a = b ∨ ∃ z, b ~>sn z ∧ a ~>* z := by
    sorry
    -- intro r1 r2
    -- induction r1 generalizing b
    -- case _ t' A b' h =>
    --   cases r2
    --   case _ => apply Or.inl rfl
    --   case _ f' r =>
    --     cases r; case _ b'' r =>
    --     apply Or.inr; exists (b''[.su t' :: +0])
    --     apply And.intro
    --     apply SnHeadRed.beta h
    --     apply Star.subst; apply Star.step Star.refl r
    --   case _ t'' r =>
    --     apply Or.inr; exists (b'[.su t'' :: +0])
    --     apply And.intro
    --     apply SnHeadRed.beta
    --     apply SN.preservation_step h r
    --     apply Red.subst_arg
    --     intro x; cases x <;> simp
    --     case _ => apply ActionRed.su r
    --     case _ => apply ActionRed.re
    -- case _ f f' a r1 ih =>
    --   cases r2
    --   case _ => cases r1
    --   case _ f'' r2 =>
    --     replace ih := ih r2
    --     cases ih
    --     case _ ih =>
    --       subst ih; apply Or.inl rfl
    --     case _ ih =>
    --       cases ih; case _ z ih =>
    --       have lem1 := SnHeadRed.app a ih.1
    --       apply Or.inr
    --       exists (z :@ a); apply And.intro lem1
    --       apply Star.congr2_1 a Term.app Red.app1 ih.2
    --   case _ a'' r2 =>
    --     apply Or.inr
    --     exists (f' :@ a''); apply And.intro
    --     apply SnHeadRed.app a'' r1
    --     apply Star.congr2_2 f' Term.app Red.app2
    --     apply Star.step Star.refl r2
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

  theorem succ : SN Red t <-> SN Red t.succ := by sorry

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

  theorem neutral_nrec :
    Neutral n ->
    SN Red z ->
    SN Red s ->
    SN Red n ->
    SN Red (Term.nrec A z s n)
  := by
    intro nh j1 j2 j3
    induction j3 generalizing z s; case _ n h1 ih1 =>
    induction j2 generalizing z; case _ s h2 ih2 =>
    induction j1; case _ z h3 ih3 =>
    apply SN.sn; case _ =>
    intro y r; cases r
    case nrec_zero => cases nh
    case nrec_succ => cases nh
    case nrec1 z' r => apply ih3 _ r
    case nrec2 s' r => apply ih2 _ r (.sn h3)
    case nrec3 n' r =>
      apply ih1 _ r _ (.sn h3) (.sn h2)
      apply Red.preservation_of_neutral_step nh r

  theorem weak_head_expansion {t b A}
    : SN Red t -> SN Red (b[.su t::+0]) -> SN Red ((:λ[A] b) :@ t)
  := by
    intro h1; induction h1 generalizing b
    case _ t h1 ih1 =>
    intro h2
    generalize zdef : b[.su t :: +0] = z at *
    induction h2 generalizing b
    case _ w h2 ih2 =>
    apply SN.sn; intro y r
    cases r
    case _ => rw [zdef]; apply SN.sn h2
    case _ q r =>
      cases r; case _ b' r =>
      have lem : b[.su t::+0] ~> b'[.su t::+0] := by
        apply Red.subst (.su t::+0) r
      apply ih2 (b'[.su t::+0]) (by rw [<-zdef]; apply lem) rfl
    case _ t' r =>
      have lem1 : SN Red w := SN.sn h2; rw [<-zdef] at lem1
      have lem2 : b[.su t::+0] ~>* b[.su t'::+0] := by
        apply Red.subst_arg; intro x
        cases x <;> simp at *
        apply ActionRed.su r
        apply ActionRed.re
      have lem3 := SN.preservation lem1 lem2
      apply ih1 t' r lem3

  theorem red_app_preservation {f f' a}
    : f ~>sn f' -> SN Red f -> SN Red a -> SN Red (f' :@ a) -> SN Red (f :@ a)
  := by
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
    sorry
    -- intro h r; induction r
    -- case _ h2 => apply weak_head_expansion h2 h
    -- case _ r ih =>
    --   have lem := subterm_app h
    --   apply red_app_preservation r (ih lem.1) lem.2 h
end SN

mutual
  @[grind]
  inductive SnNor : Term -> Prop
  | lam : SnNor t -> SnNor (:λ[A] t)
  | zero : SnNor .zero
  | succ : SnNor t -> SnNor t.succ
  | neu : SnNeu t -> SnNor t
  | red : SnRed t t' -> SnNor t' -> SnNor t

  @[grind]
  inductive SnNeu : Term -> Prop
  | var : SnNeu #x
  | app : SnNeu s -> SnNor t -> SnNeu (s :@ t)
  | nrec : SnNor z -> SnNor s -> SnNeu t -> SnNeu (.nrec A z s t)

  @[grind]
  inductive SnRed : Term -> Term -> Prop
  | beta : SnNor t -> SnRed ((:λ[A] b) :@ t) b[su t::+0]
  | zero : SnRed (.nrec A z s .zero) z
  | succ : SnRed (.nrec A z s t.succ) (s :@ (.nrec A z s t))
  | step_app : SnRed s s' -> SnRed (s :@ t) (s' :@ t)
  | step_nrec : SnRed n n' -> SnRed (.nrec A z s n) (.nrec A z s n')
end

mutual
  def SnNor.rename (r : Ren) : SnNor t -> SnNor t[r]
  | @SnNor.lam t _ th =>
    let lem : SnNor t[r.to.lift] := by
      rw [<-Ren.to_lift]
      exact .rename r.lift th
    SnNor.lam lem
  | .zero => .zero
  | .succ t => .succ (.rename r t)
  | .neu t => .neu (.rename r t)
  | .red h t' => .red (.rename r h) (.rename r t')

  def SnNeu.rename (r : Ren) : SnNeu t -> SnNeu t[r]
  | .var => .var
  | .app s t => .app (.rename r s) (.rename r t)
  | .nrec t z s => .nrec (.rename r t) (.rename r z) (.rename r s)

  def SnRed.rename (r : Ren) : SnRed t t' -> SnRed t[r] t'[r]
  | @SnRed.beta t A b th => by {
    have lem := @SnRed.beta (t[r]) A (b[.re 0 :: r ∘ +1]) (.rename r th)
    simp at lem; simp; exact lem
  }
  | .zero => .zero
  | .succ => .succ
  | .step_app h => .step_app (.rename r h)
  | .step_nrec h => .step_nrec (.rename r h)
end

mutual
  def SnNor.antirename (r : Ren) : SnNor t -> ∀ z, t = z[r] -> SnNor z := sorry

  def SnNeu.antirename (r : Ren) : SnNeu t -> ∀ z, t = z[r] -> SnNeu z := sorry

  def SnRed.antirename (r : Ren) : SnRed t t' -> ∀ z, t = z[r] -> ∃ z', t' = z'[r] ∧ SnRed z z' := sorry
end

def SnNeu.beta_var : SnNeu s -> s = t :@ .var x -> SnNeu t
| .app f a, e => by grind

theorem SnNor.beta_var : ∀ {s}, SnNor s -> ∀ {t x}, s = t :@ .var x -> SnNor t := by
  intro s sn
  apply SnNor.brecOn
    (motive_1 := λ s sn => ∀ {t x}, s = t :@ .var x -> SnNor t)
    (motive_2 := λ _ _ => True)
    (motive_3 := λ _ _ _ => True)
    sn
  case _ =>
    intro s sn ih t x e
    cases ih; all_goals try solve | injection e
    case neu sn _ =>
      apply SnNor.neu
      apply SnNeu.beta_var sn e
    case red t' t'n _ t'nb ih r rb =>
      subst e; cases rb
      case beta b _ _ ih2 =>
        apply SnNor.lam
        let r : Ren := x :: id
        have lem : b[.su #x :: +0] = b[r] := by
          subst r; rw [ren_subst_apply_eq]
          intro i y h
          cases i <;> simp at *
          case zero => exact h
          case _ z => exact h
        rw [lem] at t'n
        apply SnNor.antirename r t'n b rfl
      case step_app s' _ r rb =>
        apply SnNor.red r
        apply ih rfl
  all_goals simp

def SnNeu.weaken : SnNeu t -> Neutral t
| .var => .var
| .app f a => .app f.weaken
| .nrec _ _ n => .nrec n.weaken

def SnRed.weaken : SnRed t t' -> t ~> t'
| .beta t => .beta
| .zero => .nrec_zero
| .succ => .nrec_succ
| .step_app r => .app1 r.weaken
| .step_nrec r => .nrec3 r.weaken

mutual
  def SnNor.sound : SnNor t -> SN Red t
  | .lam h => SN.lam.1 h.sound
  | .zero => SN.sn (by grind)
  | .succ h => SN.succ.1 h.sound
  | .neu h => h.sound
  | .red r h => SN.backward_closure h.sound r.sound

  def SnNeu.sound : SnNeu t -> SN Red t
  | .var => SN.sn (by grind)
  | .app s t => SN.neutral_app s.weaken s.sound t.sound
  | .nrec z s n => SN.neutral_nrec n.weaken z.sound s.sound n.sound

  def SnRed.sound : SnRed t t' -> t ~>sn t'
  | .beta h => .beta h.sound
  | .zero => .zero
  | .succ => .succ
  | .step_app h => .app _ h.sound
  | .step_nrec h => .nrec h.sound
end

namespace SNi

  -- @[simp]
  -- abbrev SnAntiRenameLemmaType (r : Ren) : (v : SnVariant) -> (i : SnIndices v) -> Prop
  -- | .neu, t => ∀ z, t = z[r] -> SNi .neu z
  -- | .nor, t => ∀ z, t = z[r] -> SNi .nor z
  -- | .red, (t, t') =>
  --   ∀ z, t = z[r] ->
  --   ∃ z', t' = z'[r] ∧ SNi .red (z, z')

  -- theorem antirename {v i} r : SNi v i -> SnAntiRenameLemmaType r v i := by
  --   intro j; induction j generalizing r <;> simp at *
  --   case var x =>
  --     intro z h
  --     cases z <;> simp at h
  --     case _ y => apply SNi.var
  --   case app s t j1 j2 ih1 ih2 =>
  --     intro z h1; cases z <;> simp at h1
  --     case _ x => apply SNi.var
  --     case _ u v => apply SNi.app (ih1 r _ h1.1) (ih2 r _ h1.2)
  --   case lam t A j ih =>
  --     intro z h
  --     cases z <;> simp at h
  --     case _ x => apply SNi.neu; apply SNi.var
  --     case _ A' b =>
  --       cases h; case _ h1 h2 =>
  --       subst h1; apply SNi.lam
  --       replace ih := ih (r.lift) b
  --       rw [Ren.to_lift] at ih
  --       simp at ih; apply ih h2
  --   case neu t j ih =>
  --     intro z h2
  --     replace ih := ih r z h2
  --     apply SNi.neu ih
  --   case red t t' j1 j2 ih1 ih2 =>
  --     intro z h2
  --     have lem := ih1 r _ h2
  --     cases lem; case _ z' h2 =>
  --     apply SNi.red h2.2
  --     apply ih2 r _ h2.1
  --   case beta t A b j ih =>
  --     intro z h2
  --     cases z <;> simp at h2
  --     case _ x =>
  --       have lem := to_ren_is_var h2
  --       cases lem; case _ y lem =>
  --       injection lem
  --     case _ u v =>
  --       cases u <;> simp at h2
  --       case _ x =>
  --         have lem := to_ren_is_var h2.1
  --         cases lem; case _ y lem =>
  --         injection lem
  --       case _ A' u =>
  --         cases h2; case _ h1 h2 =>
  --         cases h1; case _ h1 h3 =>
  --         subst h1
  --         replace ih := ih r _ h2
  --         subst h2; subst h3; simp at *
  --         exists (u[.su v :: +0]); simp
  --         apply SNi.beta ih
  --   case step s s' t j ih =>
  --     intro z h2
  --     cases z <;> simp at h2
  --     case _ x =>
  --       have lem := to_ren_is_var h2
  --       cases lem; case _ y lem =>
  --       injection lem
  --     case _ u v =>
  --       replace ih := ih r _ h2.1
  --       cases ih; case _ z' h' =>
  --       exists (z' :@ v); simp [*]
  --       apply SNi.step (h'.2)

end SNi
