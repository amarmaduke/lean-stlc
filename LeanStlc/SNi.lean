import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.Progress

open LeanSubst

inductive SnHeadRed : Term -> Term -> Prop where
| beta {t A b} : SN Red t -> SnHeadRed ((:λ[A] b) :@ t) (b[.su t::+0])
| zero : SN Red s -> SnHeadRed (.nrec A z s .zero) z
| succ : SnHeadRed (.nrec A z s (.succ n)) (s :@ (.nrec A z s n))
| nrec : SnHeadRed n n' -> SnHeadRed (.nrec A z s n) (.nrec A z s n')
| app {f f'} a : SnHeadRed f f' -> SnHeadRed (f :@ a) (f' :@ a)

infix:80 " ~>sn " => SnHeadRed

def SnHeadRed.red_compatible {t a b} : t ~>sn a -> t ~> b -> a = b ∨ ∃ z, b ~>sn z ∧ a ~>* z
| .beta t, .beta => .inl rfl
| .beta tn, .app1 (.lam r) => .inr ⟨_, .beta tn, .subst _ (.step .refl r)⟩
| .beta (t := t) tn, .app2 (a' := a) r =>
  let h : ∀ (x : Nat), ActionRed Red ((su t :: +0) x) ((su a :: +0) x)
    | 0 => .su r
    | x + 1 => .re
  .inr ⟨_, .beta (.preservation_step tn r), Red.subst_arg h⟩
| .zero _, .nrec_zero => .inl rfl
| .zero sn, .nrec1 r => .inr ⟨_, .zero sn, .step .refl r⟩
| .zero sn, .nrec2 r => .inr ⟨_, .zero (sn.preservation_step r), .refl⟩
| .succ, .nrec_succ => .inl rfl
| .succ, .nrec1 r => .inr ⟨_, .succ, .step .refl (.app2 $ .nrec1 r)⟩
| .succ, .nrec2 r =>
  let r1 := Star.step .refl r
  let r2 := Star.step .refl (.nrec2 r)
  .inr ⟨_, .succ, .congr2 Term.app .app1 .app2 r1 r2⟩
| .succ, .nrec3 (.succ r) => .inr ⟨_, .succ, .step .refl (.app2 $ .nrec3 r)⟩
| .nrec r, .nrec1 r2 => .inr ⟨_, .nrec r, .step .refl $ .nrec1 r2⟩
| .nrec r, .nrec2 r2 => .inr ⟨_, .nrec r, .step .refl $ .nrec2 r2⟩
| .nrec r, .nrec3 r2 =>
  match red_compatible r r2 with
  | .inl ih => .inl (by grind)
  | .inr ⟨z, ih1, ih2⟩ => .inr ⟨_, .nrec ih1, .congr3_3 _ _ (.nrec _) .nrec3 ih2⟩
| .app a r, .app1 r2 =>
  match red_compatible r r2 with
  | .inl ih => .inl (by grind)
  | .inr ⟨z, ih1, ih2⟩ =>
    .inr ⟨z :@ a, .app a ih1, .congr2_1 a .app .app1 ih2⟩
| .app (f' := f') a r, .app2 (a' := a') r2 =>
  .inr ⟨f' :@ a', .app a' r, .congr2_2 f' .app .app2 (.step .refl r2)⟩

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

  theorem subterm_nrec : SN Red (.nrec A z s n) -> SN Red z ∧ SN Red s ∧ SN Red n := by
    intro j; generalize wdef : Term.nrec A z s n = w at j
    induction j generalizing z s n; case _ w h ih =>
    subst wdef; apply And.intro _; apply And.intro
    case _ =>
      apply SN.sn; intro s' r
      replace ih := ih (.nrec A z s' n) (Red.nrec2 r) rfl
      apply ih.2.1
    case _ =>
      apply SN.sn; intro n' r
      replace ih := ih (.nrec A z s n') (Red.nrec3 r) rfl
      apply ih.2.2
    case _ =>
      apply SN.sn; intro z' r
      replace ih := ih (.nrec A z' s n) (Red.nrec1 r) rfl
      apply ih.1

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

  theorem succ : SN Red t <-> SN Red t.succ := by
    apply Iff.intro
    case _ =>
      intro h; induction h
      case _ t h ih =>
      apply SN.sn; intro y r
      cases r; case _ t' r =>
      apply ih _ r
    case _ =>
      intro h
      generalize zdef : t.succ = z at *
      induction h generalizing t
      case _ x h ih =>
      apply SN.sn; intro y r
      subst zdef
      apply ih y.succ (Red.succ r) rfl

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

  theorem zero_expansion : SN Red s -> SN Red z -> SN Red (.nrec A z s .zero) := by
    intro h1 h2
    induction h2 generalizing s; case _ z hz ihz =>
    induction h1; case _ s hs ihs =>
    apply SN.sn; case _ =>
    intro y r; cases r
    case nrec_zero => apply SN.sn hz
    case nrec1 z' r =>
      apply ihz _ r
      apply SN.sn hs
    case nrec2 s' r => apply ihs _ r
    case nrec3 n' r => cases r

  theorem succ_expansion : SN Red (s :@ .nrec A z s n) -> SN Red z -> SN Red s -> SN Red n -> SN Red (.nrec A z s n.succ) := by
    intro h j1 j2 j3
    induction j3 generalizing z s; case _ n j3 ih3 =>
    induction j2 generalizing z; case _ s j2 ih2 =>
    induction j1; case _ z j1 ih1 =>
    apply SN.sn; case _ =>
    intro y r; cases r
    case nrec_succ n => exact h
    case nrec1 z' r =>
      apply ih1 _ r
      apply SN.preservation_step h
      apply Red.app2
      apply Red.nrec1 r
    case nrec2 s' r =>
      apply ih2 _ r
      apply SN.preservation h
      apply Star.congr2 Term.app Red.app1 Red.app2
      apply Star.step .refl r
      apply Star.step .refl
      apply Red.nrec2 r
      apply SN.sn j1
    case nrec3 n' r =>
      cases r; case _ n' r =>
      apply ih3 _ r _ (SN.sn j1) (SN.sn j2)
      apply SN.preservation_step h
      apply Red.app2
      apply Red.nrec3 r

  theorem backward_closure_app {f f' a}
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

  theorem backward_closure_nrec
    : n ~>sn n' -> SN Red z -> SN Red s -> SN Red n -> SN Red (.nrec A z s n') -> SN Red (.nrec A z s n)
  := by
    intro r1 h1 h2 h3 h4
    induction h3 generalizing z s n'; case _ n hn ihn =>
    induction h2 generalizing z; case _ s hs ihs =>
    induction h1; case _ z hz ihz =>
    apply SN.sn; intro y r2; case _ =>
    cases r2
    case nrec_zero => cases r1
    case nrec_succ => cases r1
    case nrec1 z' r =>
      apply ihz z' r
      apply SN.preservation_step h4
      apply Red.nrec1 r
    case nrec2 s' r =>
      apply ihs s' r (SN.sn hz)
      apply SN.preservation_step h4
      apply Red.nrec2 r
    case nrec3 n'' r =>
      have lem1 := SnHeadRed.red_compatible r1 r
      cases lem1
      case _ lem1 => subst lem1; exact h4
      case _ lem1 =>
        obtain ⟨w, lem1, lem2⟩ := lem1
        apply ihn n'' r lem1 (SN.sn hz) (SN.sn hs)
        apply SN.preservation h4
        apply Star.congr3_3 _ _ (Term.nrec _) Red.nrec3 lem2

  theorem backward_closure {t' t} : SN Red t' -> t ~>sn t' -> SN Red t := by
    intro h r; induction r
    case beta h2 => apply weak_head_expansion h2 h
    case app r ih =>
      have lem := subterm_app h
      apply backward_closure_app r (ih lem.1) lem.2 h
    case zero h2 => apply zero_expansion h2 h
    case succ =>
      obtain ⟨h1, h2⟩ := subterm_app h
      obtain ⟨h3, h4, h5⟩ := subterm_nrec h2
      apply succ_expansion h h3 h4 h5
    case nrec r ih =>
      obtain ⟨h1, h2, h3⟩ := subterm_nrec h
      apply backward_closure_nrec r h1 h2 (ih h3) h
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
  | zero : SnNor s -> SnRed (.nrec A z s .zero) z
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
  | .succ t => .succ (t.rename r)
  | .neu t => .neu (t.rename r)
  | .red h t' => .red (h.rename r) (t'.rename r)

  def SnNeu.rename (r : Ren) : SnNeu t -> SnNeu t[r]
  | .var => .var
  | .app s t => .app (s.rename r) (t.rename r)
  | .nrec t z s => .nrec (t.rename r) (z.rename r) (s.rename r)

  def SnRed.rename (r : Ren) : SnRed t t' -> SnRed t[r] t'[r]
  | @SnRed.beta t A b th => by {
    have lem := @SnRed.beta (t[r]) A (b[.re 0 :: r ∘ +1]) (.rename r th)
    simp at lem; simp; exact lem
  }
  | .zero h => .zero (h.rename r)
  | .succ => .succ
  | .step_app h => .step_app (h.rename r)
  | .step_nrec h => .step_nrec (h.rename r)
end

mutual
  def SnNor.antirename (r : Ren) : SnNor t -> ∀ z, t = z[r] -> SnNor z
  | @SnNor.lam t A tn, :λ[A'] t', e =>
    have ⟨e1, e2⟩ : A = A' ∧ t = t'[r.lift] := by grind
    have tn' := tn.antirename r.lift _ e2
    .lam tn'
  | .zero, .zero, e => .zero
  | @SnNor.succ t tn, (.succ t'), e =>
    have e : t = t'[r] := by grind
    .succ (tn.antirename r _ e)
  | .neu t, z, e => .neu (t.antirename r _ e)
  | .red h t', z, e =>
    let ⟨w, e, h'⟩ := h.antirename r _ e
    let t'' := SnNor.antirename r t' _ e
    .red h' t''

  def SnNeu.antirename (r : Ren) : SnNeu t -> ∀ z, t = z[r] -> SnNeu z
  | .var, #z, e => .var
  | @SnNeu.app s t sn tn, f :@ a, e =>
    let ⟨e1, e2⟩ : s = f[r] ∧ t = a[r] := by grind
    let sn' := sn.antirename r _ e1
    let tn' := tn.antirename r _ e2
    .app sn' tn'
  | @SnNeu.nrec z s n A zn sn nn, .nrec A' z' s' n', e =>
    let ⟨e1, e2, e3, e4⟩: A = A' ∧ z = z'[r] ∧ s = s'[r] ∧ n = n'[r] := by grind
    let zn' := zn.antirename r _ e2
    let sn' := sn.antirename r _ e3
    let nn' := nn.antirename r _ e4
    .nrec zn' sn' nn'

  -- this beta case is REALLY crazy (subst breaks termination checks)
  def SnRed.antirename (r : Ren) : SnRed t t' -> ∀ z, t = z[r] -> ∃ z', t' = z'[r] ∧ SnRed z z'
  | .beta (t := t) (b := b) tn, .app (.lam A b') t', e =>
    let ⟨e1, e2⟩ : t = t'[r] ∧ b = b'[re 0::r ∘ +1] := by grind
    let tn' := tn.antirename r _ e1
    -- ⟨b'[su t'::+0], (by subst e1 e2; simp), .beta tn'⟩
    ⟨b'[su t'::+0], (by rw [e1, e2]; simp), .beta tn'⟩
  | @SnRed.zero s A z h, .nrec A' z' s' .zero, e =>
    let ⟨e1, e2, e3⟩: A = A' ∧ z = z'[r] ∧ s = s'[r] := by grind
    let h' := h.antirename r _ e3
    ⟨z', e2, .zero h'⟩
  | @SnRed.succ A z s n, .nrec A' z' s' (.succ n'), e =>
    let ⟨e1, e2, e3, e4⟩: A = A' ∧ z = z'[r] ∧ s = s'[r] ∧ n = n'[r] := by grind
    ⟨s' :@ .nrec A' z' s' n', (by grind), .succ⟩
  | @SnRed.step_app s s' t h, f :@ a, e =>
    let ⟨e1, e2⟩ : s = f[r] ∧ t = a[r] := by grind
    have ⟨z, e, h2⟩ := h.antirename r _ e1
    ⟨z :@ a, (by grind), .step_app h2⟩
  | @SnRed.step_nrec n n' A z s h, .nrec A' z' s' n'', e =>
    let ⟨e1, e2, e3, e4⟩ : A = A' ∧ z = z'[r] ∧ s = s'[r] ∧ n = n''[r] := by grind
    have ⟨w, e, h2⟩ := h.antirename r _ e4
    ⟨.nrec A' z' s' w, (by grind), .step_nrec h2⟩
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
| .zero _ => .nrec_zero
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
  | .zero h => .zero h.sound
  | .succ => .succ
  | .step_app h => .app _ h.sound
  | .step_nrec h => .nrec h.sound
end
