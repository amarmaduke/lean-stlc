import LeanSubst
import LeanStlc.Reduction

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

  theorem weak_head_expansion {t b A} :
    SN Red t ->
    SN Red (b[.su t::+0]) ->
    SN Red ((:λ[A] b) :@ t)
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

  theorem succ_expansion :
    SN Red (s :@ .nrec A z s n) ->
    SN Red z ->
    SN Red s ->
    SN Red n ->
    SN Red (.nrec A z s n.succ)
  := by
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

  theorem backward_closure_app :
    f ~>sn f' ->
    SN Red f ->
    SN Red a ->
    SN Red (f' :@ a) ->
    SN Red (f :@ a)
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

  theorem backward_closure_nrec :
    n ~>sn n' ->
    SN Red z ->
    SN Red s ->
    SN Red n ->
    SN Red (.nrec A z s n') ->
    SN Red (.nrec A z s n)
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
