import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing

open LeanSubst

namespace Term
  @[simp]
  def is_lam : Term -> Bool
  | lam _ _ => true
  | _ => false

  @[simp]
  def destruct_lam : Term -> Option (Ty × Term)
  | lam A t => some (A, t)
  | _ => none

  @[simp]
  def is_nat : Term -> Bool
  | zero => true
  | succ _ => true
  | _ => false

  @[simp]
  def destruct_nat : Term -> Option (Term ⊕ Unit)
  | zero => some (.inr ())
  | succ n => some (.inl n)
  | _ => none
end Term

inductive Value : Term -> Prop where
| var : Value #x
| app :
  Value f ->
  Value a ->
  f.destruct_lam = none ->
  Value (f :@ a)
| lam :
  Value t ->
  Value (:λ[A] t)
| nrec :
  Value z ->
  Value s ->
  Value n ->
  n.destruct_nat = none ->
  Value (.nrec A z s n)
| zero : Value Term.zero
| succ : Value n -> Value (Term.succ n)

def Value.sound : Value t -> ∀ t', ¬ (t ~> t')
| app f _ _, _, .app1 r => sound f _ r
| app _ a _, _, .app2 r => sound a _ r
| lam t, _, .lam r => sound t _ r
| nrec z _ _ _, _, .nrec1 r => sound z _ r
| nrec _ s _ _, _, .nrec2 r => sound s _ r
| nrec _ _ n _, _, .nrec3 r => sound n _ r
| succ n, _, .succ r => sound n _ r

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
  case _ =>
    sorry
  case _ =>
    sorry
  all_goals sorry

def Term.is_lam_value : t.is_lam -> ∃ A b, t = :λ[A] b := by
  induction t <;> simp [is_lam]

def Term.progress : (t : Term) -> Value t ∨ (∃ t', t ~> t')
| var x => .inl .var
| app f a =>
  match h : f.destruct_lam, progress f, progress a with
  | some (A, b), _, _ => .inr ⟨b[su a::+0], by simp at h; grind⟩
  | none, .inl fv, .inl av => .inl (.app fv av h)
  | _, .inr ⟨f', r⟩, _ => .inr ⟨app f' a, .app1 r⟩
  | _, _, .inr ⟨a', r⟩ => .inr ⟨app f a', .app2 r⟩
| lam A t =>
  match progress t with
  | .inl tv => .inl (.lam tv)
  | .inr ⟨t', r⟩ => .inr ⟨lam A t', .lam r⟩
| zero => .inl .zero
| succ n =>
  match progress n with
  | .inl nv => .inl (.succ nv)
  | .inr ⟨n', r⟩ => .inr ⟨succ n', .succ r⟩
| nrec A z s n =>
  match h : n.destruct_nat, progress z, progress s, progress n with
  | some (.inr ()), _, _, _ => .inr ⟨z, by simp at h; grind⟩
  | some (.inl n), _, _, _ => .inr ⟨s :@ nrec A z s n, by simp at h; grind⟩
  | none, .inl zv, .inl sv, .inl nv => .inl (.nrec zv sv nv h)
  | _, .inr ⟨z', r⟩, _, _ => .inr ⟨nrec A z' s n, .nrec1 r⟩
  | _, _, .inr ⟨s', r⟩, _ => .inr ⟨nrec A z s' n, .nrec2 r⟩
  | _, _, _, .inr ⟨n', r⟩ => .inr ⟨nrec A z s n', .nrec3 r⟩

  -- induction t
  -- case var x => apply Or.inl; apply Value.var
  -- case app f a ih1 ih2 =>
  --   cases ih1
  --   case _ ih1 =>
  --     cases ih2
  --     case _ ih2 =>
  --       cases f
  --       case var x =>
  --         apply Or.inl
  --         apply Value.app ih1 ih2
  --         simp
  --       case lam A t =>
  --         apply Or.inr
  --         exists (t[.su a :: +0])
  --         apply Red.beta
  --       case app f b =>
  --         apply Or.inl
  --         apply Value.app ih1 ih2
  --         simp
  --     case _ ih2 =>
  --       cases ih2; case _ a' ih2 =>
  --       apply Or.inr; exists (f :@ a')
  --       apply Red.app2 ih2
  --   case _ ih1 =>
  --     cases ih1; case _ f' ih1 =>
  --     apply Or.inr; exists (f' :@ a)
  --     apply Red.app1 ih1
  -- case lam A t ih =>
  --   cases ih
  --   case _ ih =>
  --     apply Or.inl
  --     apply Value.lam ih
  --   case _ ih =>
  --     cases ih; case _ t' ih =>
  --     apply Or.inr; exists (:λ[A] t')
  --     apply Red.lam ih
