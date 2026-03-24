import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing
import LeanStlc.Progress
import LeanStlc.SN

open LeanSubst

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
