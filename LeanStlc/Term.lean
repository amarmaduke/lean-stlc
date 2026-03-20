
import LeanSubst

inductive Ty : Type where
| base : Ty
| arrow : Ty -> Ty -> Ty
| nat : Ty

notation "⊤" => Ty.base
infixr:40 " -t> " => Ty.arrow

protected def Ty.repr (a : Ty) (p : Nat) : Std.Format :=
  match a with
  | .base => "⊤"
  | .arrow .base B => Ty.repr .base p ++ " -> " ++ Ty.repr B p
  | .arrow A B => "(" ++ Ty.repr A p ++ ") -> " ++ Ty.repr B p
  | .nat => "ℕ"

instance : Repr Ty where
  reprPrec := Ty.repr

inductive Term where
| var : Nat -> Term
| app : Term -> Term -> Term
| lam : Ty -> Term -> Term
| zero : Term
| succ : Term -> Term
| nrec : Ty -> Term -> Term -> Term -> Term

protected def Term.repr (a : Term) (p : Nat) : Std.Format :=
  match a with
  | .var x => "#" ++ Nat.repr x
  | .app f a => "(" ++ Term.repr f p ++ " " ++ Term.repr a p ++ ")"
  | .lam _ t => "(λ " ++ Term.repr t p ++ ")"
  | .zero => "'0"
  | .succ n => "S(" ++ Term.repr n p ++ ")"
  | .nrec A z s n => "(R " ++ Ty.repr A p ++ Term.repr z p ++ Term.repr s p ++ Term.repr n p ++ ")"

instance : Repr Term where
  reprPrec := Term.repr

open LeanSubst

prefix:max "#" => Term.var
infixl:65 " :@ " => Term.app
notation ":λ[" A "] " t => Term.lam A t

open LeanSubst

@[coe]
def Term.from_action : Subst.Action Term -> Term
| .re y => #y
| .su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (+0 n) = #n := by
  simp [from_action, Subst.id]

@[simp]
theorem Term.from_action_succ {n} : from_action (+1 n) = #(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Term.from_acton_re {n} : from_action (.re n) = #n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t} : from_action (.su t) = t := by simp [from_action]

instance instCoe_SubstActionTerm_Term : Coe (Subst.Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : Ren) : Term -> Term
| #x => #(r x)
| t1 :@ t2 => rmap r t1 :@ rmap r t2
| :λ[A] t => :λ[A] rmap r.lift t
| zero => zero
| succ n => succ (rmap r n)
| nrec A z s n => nrec A (rmap r z) (rmap r s) (rmap r n)

instance : RenMap Term where
  rmap := Term.rmap

@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| #x => σ x
| t1 :@ t2 => smap σ t1 :@ smap σ t2
| :λ[A] t => :λ[A] smap σ.lift t
| zero => zero
| succ n => succ (smap σ n)
| nrec A z s n => nrec A (smap σ z) (smap σ s) (smap σ n)

instance SubstMap_Term : SubstMap Term Term where
  smap := Term.smap

@[simp, grind =]
theorem subst_var {σ x} : (#x)[σ] = σ x := by simp [SubstMap.smap]

@[simp, grind =]
theorem subst_app {σ t1 t2} : (t1 :@ t2)[σ] = t1[σ] :@ t2[σ] := by simp [SubstMap.smap]

@[simp, grind =]
theorem subst_lam {σ A t} : (:λ[A] t)[σ] = :λ[A] t[σ.lift] := by simp [SubstMap.smap]

@[simp, grind =]
theorem subst_zero : (Term.zero)[σ] = Term.zero := by simp [SubstMap.smap]

@[simp, grind =]
theorem subst_succ : (Term.succ n)[σ] = Term.succ (n[σ]) := by simp [SubstMap.smap]

@[simp, grind =]
theorem subst_nrec : (Term.nrec A z s n)[σ] = .nrec A (z[σ]) (s[σ]) (n[σ]) := by simp [SubstMap.smap]

@[simp]
theorem Term.from_action_compose {x} {σ τ : Subst Term}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Term.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Term.from_action]

theorem apply_id {t : Term} : t[+0] = t := by
  induction t
  all_goals try (simp at * <;> try simp [*])

instance : SubstMapId Term Term where
  apply_id := apply_id

theorem apply_stable (r : Ren) (σ : Subst Term)
  : r = σ -> rmap (T := Term) r = smap σ
:= by subst_solve_stable r, σ

instance SubstMapStable_Term : SubstMapStable Term where
  apply_stable := apply_stable

theorem apply_compose {s : Term} {σ τ : Subst Term} : s[σ][τ] = s[σ ∘ τ] := by
  subst_solve_compose Term, s, σ, τ

instance SubstMapCompose_Term : SubstMapCompose Term Term where
  apply_compose := apply_compose

inductive Neutral : Term -> Prop where
| var : Neutral #x
| app : Neutral f -> Neutral (f :@ a)
| nrec : Neutral n -> Neutral (.nrec A z s n)

theorem to_ren_is_var {t : Term} {r : Ren} : t = Term.from_action (r.to x) -> ∃ y, t = #y := by
  intro h
  generalize zdef : r.to x = z at *
  cases z <;> simp at *
  case _ i => subst h; exists i
  case _ t' => subst h; simp [Ren.to] at zdef

theorem ren_subst_apply_eq_lift {r : Ren} {σ : Subst Term} :
  (∀ i x, r i = x -> σ i = #x ∨ σ i = .re x) ->
  ∀ i x, r.lift i = x -> σ.lift i = #x ∨ σ.lift i = .re x
:= by
  intro h1 i x h2
  cases i <;> simp [Ren.lift] at *
  case zero => exact h2
  case succ i =>
    cases (h1 i)
    case _ h =>
      simp [Subst.compose]
      generalize zdef : σ i = z at *
      cases z <;> simp at *
      case _ y => subst h; exact h2
      case _ t => subst h; simp; exact h2
    case _ h =>
      simp [Subst.compose]
      generalize zdef : σ i = z at *
      cases z <;> simp at *
      case _ y => subst h; exact h2

theorem ren_subst_apply_eq {t : Term} {r : Ren} {σ : Subst Term} :
  (∀ i x, r i = x -> σ i = #x ∨ σ i = .re x) ->
  t[r] = t[σ]
:= by
  intro h
  induction t generalizing r σ <;> simp
  case var x =>
    have lem := h x (r x) rfl
    cases lem
    case _ lem =>
      rw [lem]
      simp [Term.from_action, Ren.to]
    case _ lem =>
      rw [lem]
      simp [Term.from_action, Ren.to]
  case lam A t ih =>
    replace ih := @ih r.lift σ.lift (ren_subst_apply_eq_lift h)
    grind
  all_goals grind

@[coe]
def Ty.from_action : Subst.Action Ty -> Ty
| .re _ => base
| .su t => t
