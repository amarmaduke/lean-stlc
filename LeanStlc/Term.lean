
import LeanSubst

inductive Ty : Type where
| base : Ty
| arrow : Ty -> Ty -> Ty

notation "⊤" => Ty.base
infixr:40 " -t> " => Ty.arrow

protected def Ty.repr (a : Ty) (p : Nat) : Std.Format :=
  match a with
  | .base => "⊤"
  | .arrow .base B => Ty.repr .base p ++ " -> " ++ Ty.repr B p
  | .arrow A B => "(" ++ Ty.repr A p ++ ") -> " ++ Ty.repr B p

instance : Repr Ty where
  reprPrec := Ty.repr

inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam : Ty -> Term -> Term

protected def Term.repr (a : Term) (p : Nat) : Std.Format :=
  match a with
  | .var x => "#" ++ Nat.repr x
  | .app f a => "(" ++ Term.repr f p ++ " " ++ Term.repr a p ++ ")"
  | .lam _ t => "(λ " ++ Term.repr t p ++ ")"

instance : Repr Term where
  reprPrec := Term.repr

open LeanSubst

instance instPrefixHash_Term : PrefixHash Term where
  hash := Term.var

namespace Term
  @[simp]
  theorem var_def : Term.var x = #x := by simp [PrefixHash.hash]

  @[simp]
  theorem var_eq : (PrefixHash.hash (T := Term) x = #y) = (x = y) := by
    simp [-var_def, PrefixHash.hash]
end Term

infixl:65 " :@ " => Term.app
notation ":λ[" A "] " t => Term.lam A t

@[simp]
def smap (lf : Subst.Lift Term) (f : Nat -> Subst.Action Term) : Term -> Term
| .var x =>
  match f x with
  | .re y => #y
  | .su t => t
| t1 :@ t2 => smap lf f t1 :@ smap lf f t2
| :λ[A] t => :λ[A] smap lf (lf f) t

instance SubstMap_Term : SubstMap Term where
  smap := smap

@[simp]
instance HasSimpleVar_Term : HasSimpleVar Term where
  var := Term.var
  smap := by solve_simple_var_smap

@[simp]
theorem subst_var {σ : Subst Term} : (#x)[σ] = match σ x with | .re y => #y | .su t => t := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_app : (t1 :@ t2)[σ] = t1[σ] :@ t2[σ] := by
  unfold Subst.apply; simp [SubstMap.smap]

@[simp]
theorem subst_lam : (:λ[A] t)[σ] = :λ[A] t[σ.lift] := by
  unfold Subst.apply; simp [SubstMap.smap]

theorem apply_id {t : Term} : t[I] = t := by
  induction t
  all_goals (simp at * <;> try simp [*])

theorem apply_stable {r : Ren} {σ : Subst Term}
  : r.to = σ -> Ren.apply r = Subst.apply σ
:= by solve_stable r, σ

instance SubstMapStable_Term : SubstMapStable Term where
  apply_id := apply_id
  apply_stable := apply_stable

theorem apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
  solve_compose Term, s, σ, τ

instance SubstMapCompose_Term : SubstMapCompose Term where
  apply_compose := apply_compose

inductive Neutral : Term -> Prop where
| var : Neutral #x
| app : Neutral f -> Neutral (f :@ a)

namespace Term
  @[simp]
  def from_action : Subst.Action Term -> Term
  | .su t => t
  | .re k => #k
end Term

prefix:max "↑" => Term.from_action
