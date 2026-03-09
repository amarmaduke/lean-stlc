import LeanSubst
import LeanStlc.Term
import LeanStlc.Reduction
import LeanStlc.Model
import LeanStlc.Typing
import LeanStlc.Progress

open LeanSubst

def SnModelSet := Term -> Prop

def ℛ (S : SnModelSet) : SnModelSet
| t => ∀ (r:Ren), S t[r]

@[simp]
def is_lam : Term -> Bool
| .lam _ _ => true
| _ => false

@[simp]
def is_succ : Term -> Bool
| .succ _ => true
| _ => false

inductive ℒ (S : SnModelSet) : SnModelSet where
| lift {t : Term} :
  (is_lam t -> ℛ S t) ->
  (is_succ t -> ℛ S t) -> --originally was only S t
  (∀ {t' : Term}, t ~> t'-> ℒ S t') ->
  ℒ S t

inductive NatLike : SnModelSet where
| zero : NatLike .zero
| succ {n} : NatLike n -> NatLike (.succ n)

@[simp]
abbrev 𝒜 (A B : SnModelSet) : SnModelSet := λ t => ∀ a, ℒ A a -> ℒ B t[su a::+0]

@[simp]
instance : Model SnModelSet where
  A A B := fun
    | .lam _ t => 𝒜 A B t
    | _ => False
  P :=  fun t => SN Red t
  N := fun t => NatLike t

def ℰ A := ℒ ⟦ A ⟧

def 𝒞 (Γ : List Ty) (σ : Subst Term) : Prop :=
  ∀ i, ∀ T, Γ[i]? = .some T -> ℰ T (σ i)

@[simp]
def SemanticTyping (Γ : List Ty) (t : Term) (A : Ty) :=
  ∀ σ, 𝒞 Γ σ -> ℰ A t[σ]

local notation:170 Γ:170 " ⊨ " t:170 " : " A:170 => SemanticTyping Γ t A

namespace ℒ

  theorem sound : ℒ A t -> SN Red t := by
    intro h
    induction h
    case _ t' j2 j1 ih =>
      apply SN.sn
      intro y j3
      apply ih
      apply j3

  theorem preservation : ℒ A t -> t ~> t' -> ℒ A t' := by
    intro h1 h2
    cases h1
    case _ h1 h3 =>
      apply h3
      apply h2

  theorem var x : ℒ A #x := by
    apply ℒ.lift
    case _ =>
      simp
    case _ =>
      intro h
      cases h
    case _ =>
      intro t' h
      cases h

  theorem Red.antirename {s t : Term} (r : Ren) : s[r] ~> t -> ∃ z, s ~> z ∧ t = z[r] := by
    intro h
    generalize wdef : s[r] = w at *
    induction h generalizing s r
    case _ T a b =>
      cases s
      case _ n =>
        simp [Ren.to] at wdef
      case _ a' b' =>
        simp at wdef
        rcases wdef with ⟨e1, e2⟩
        subst e2
        cases a'
        case _ n =>
          cases e1
        case _ =>
          cases e1
        case _ T' t' =>
          exists (t'[su b'::+0])
          apply And.intro
          case _ =>
            apply Red.beta
          case _ =>
            simp
            simp at e1
            rcases e1 with ⟨left, right⟩
            subst right
            simp
        case _ =>
          cases e1
        case _ =>
          cases e1
        case _ =>
          cases e1
      case _ =>
        simp [Ren.to] at wdef
      case _ =>
        cases wdef
      case _ =>
        cases wdef
      case _ =>
        cases wdef
    case _ f f' a h ih =>
      cases s
      case _ =>
        cases wdef
      case _ f'' a' =>
        simp at wdef
        rcases wdef with ⟨e1,e2⟩
        subst e1 e2
        replace ih := @ih f'' r rfl
        rcases ih
        case _ g h2 =>
          rcases h2 with ⟨e1,e2⟩
          exists (g :@ a')
          apply And.intro
          case _ =>
            apply Red.app1 e1
          case _ =>
            simp
            apply e2
      case _ =>
        cases wdef
      case _ =>
        cases wdef
      case _ =>
        cases wdef
      case _ =>
        cases wdef
    case _ a a' f h ih =>
      cases s <;> simp [Ren.to] at *
      case _ f' a'' =>
        rcases wdef with ⟨e1,e2⟩
        replace ih := @ih a'' r e2
        rcases ih with ⟨z,e3, e4⟩
        exists (f' :@ z)
        apply And.intro
        case _ =>
          apply Red.app2 e3
        case _ =>
          simp
          apply And.intro; subst e1; rfl; apply e4
    case _ T t' t'' h ih =>
      cases s <;> simp at *
      case _ n =>
        rcases wdef with ⟨e1,e2⟩
      case _ A a =>
        rcases wdef with ⟨e1,e2⟩
        subst e1 e2
        replace ih := @ih a r.lift
        rw [Ren.to_lift] at ih
        simp at ih
        rcases ih with ⟨z, e1, e2⟩
        subst e2
        exists (:λ[A] z)
        apply And.intro
        case _ => apply Red.lam; apply e1
        case _ => simp
    case _  n n' re ih =>
      cases s
      case _ n =>
        cases wdef
      case _ =>
        cases wdef
      case _ =>
        cases wdef
      case _ =>
        cases wdef
      case _ n'' =>
        simp at wdef
        replace ih := @ih n'' r wdef
        rcases ih with ⟨z, e1, e2⟩
        apply Exists.intro z.succ
        apply And.intro; apply Red.succ; apply e1; simp; apply e2
      case _ =>
        cases wdef
    case _ A z s' =>
      cases s
      case nrec A' z' s'' n' =>
        simp at wdef
        rcases wdef with ⟨e1, e2, e3, e4⟩
        subst e1
        apply Exists.intro z'
        apply And.intro
        case _ =>
          cases n'
          all_goals try (cases e4)
          apply Red.nrec_zero
        case _ =>
          symm at e2; exact e2
      all_goals try (cases wdef)
    case _ A z s' n =>
      cases s
      all_goals try (cases wdef)
      case _ A' z' s'' n' =>
        simp at wdef
        rcases wdef with ⟨e1,e2,e3,e4⟩
        subst e1 e2 e3
        cases n'
        all_goals try (cases e4)
        case _ n' =>
          apply Exists.intro (s'' :@ (Term.nrec A' z' s'' n'))
          apply And.intro; apply Red.nrec_succ
          simp
          rfl
    case _  z z' A s' n re ih =>
      cases s
      case nrec A' z'' s n' =>
        simp at wdef
        rcases wdef with ⟨e1,e2,e3,e4⟩
        subst e1 e2 e3
        replace ih := @ih z'' r rfl
        rcases ih with ⟨z, e1, e2⟩
        apply Exists.intro (Term.nrec A' z s n')
        apply And.intro; apply Red.nrec1; apply e1; simp
        apply And.intro; apply e2; subst e4; rfl
      all_goals try (cases wdef)
    case _ s' s'' A z n re ih =>
      cases s
      case nrec A' z' s''' n' =>
        simp at wdef
        rcases wdef with ⟨e1,e2,e3,e4⟩
        subst e1 e2 e3
        replace ih := @ih s''' r rfl
        rcases ih with ⟨s, e1, e2⟩
        apply Exists.intro (Term.nrec A' z' s n')
        apply And.intro; apply Red.nrec2; apply e1; simp; apply And.intro; apply e2; subst e4; rfl
      all_goals try (cases wdef)
    case _ n n' A z s' re ih =>
      cases s
      case nrec A' z' s'' n'' =>
        simp at wdef
        rcases wdef with ⟨e1,e2,e3,e4⟩
        subst e1 e2 e3
        replace ih := @ih n'' r e4
        rcases ih with ⟨z, e1, e2⟩
        apply Exists.intro (Term.nrec A' z' s'' z)
        apply And.intro; apply Red.nrec3 e1; simp; apply e2
      all_goals try (cases wdef)


  theorem rename (r : Ren) : ℒ A t -> ℒ A t[r] := by
    intro h
    induction h
    case _ t' h1 h2 ih1 ih2 =>
      apply ℒ.lift
      case _ =>
        intro h3
        cases t'
        case _ n =>
          simp [Ren.to] at h3
        case _ =>
          simp at h3
        case _ A' t' =>
          simp only [ℛ] at *
          intro r'
          replace h1 := h1 h3 (r' ∘ r)
          simp at *
          apply h1
        case _ =>
          cases h3
        case _ =>
          cases h3
        case _ =>
          cases h3
      case _ =>
        intro h3
        cases t'
        case succ n =>
          simp at h2
          simp only [ℛ] at *
          intro r'
          simp at *
          apply h2
        all_goals try (cases h3)
      case _ =>
        intro t'' h5
        have lem := Red.antirename r h5
        rcases lem with ⟨z, e1, e2⟩
        subst e2
        apply ih2 e1

end ℒ

namespace ℛ

  theorem lam : ℛ ⟦A -t> B⟧ (:λ[C] b) <-> ∀ (r:Ren) a, ℰ A a -> ℰ B b[su a::r] := by
  apply Iff.intro
  case _ =>
    intro h1 r a h2
    simp only [ℛ] at h1
    simp only [ℰ] at *
    apply ℒ.lift
    case _ =>
      intro h3
      simp at h1
      simp only [ℛ]
      intro r'
      simp
      replace h1 := h1 (r) a h2
      simp at h1
      cases h1
      case _ h4 h5 h6 =>
        replace h4 := h4 h3
        simp only [ℛ] at h4
        replace h4 := h4 r'
        simp at h4; apply h4
    case _ =>
      intro h3
      simp at h1
      replace h1 := h1 (r) a h2
      simp at h1
      cases h1
      case _ j1 j2 j3 =>
        replace j2 := j2 h3; apply j2
    case _ =>
      intro t' h3
      apply ℒ.lift
      case _ =>
        intro h4
        simp only [ℛ]
        intro r'
        simp at h1
        replace h1 := h1 r a h2
        cases h1
        case _ h5 h6 =>
          replace h6 := @h6 t' h3
          cases h6
          case _ h6 h7 h8 h9 =>
            replace h7 := h7 h4
            simp only [ℛ] at h7
            apply h7
      case _ =>
        intro h4
        simp at h1
        replace h1 := h1 r a h2
        cases h1
        case _ j1 j2 j3 =>
          replace j3 := @j3 t' h3
          cases j3
          case _ w1 w2 w3 =>
            apply w2 h4
      case _ =>
        intro t'' h4
        simp at h1
        replace h1 := h1 r a h2
        cases h1
        case _ h5 h6 =>
          replace h6 := @h6 t' h3
          cases h6
          case _ h6 h7 =>
            replace h7 := @h7 t'' h4; apply h7
  case _ =>
    intro h1
    simp only [ℛ]
    intro r
    simp
    intro a h2
    apply ℒ.lift
    case _ =>
      intro h3
      simp only [ℰ] at h1
      replace h1 := h1 r a h2
      cases h1
      case _ h4 h5 h6 => apply h4; apply h3
    case _ =>
      intro h3
      replace h1 := h1 r a h2
      simp only [ℰ] at h1
      cases h1
      case _ j1 j2 j3 =>
        apply j2 h3
    case _ =>
      intro t h3
      replace h1 := h1 r a h2
      cases h1
      case _ h4 h5 =>
        apply h5; apply h3

end ℛ

namespace 𝒞

  theorem term_su : ℰ A t -> 𝒞 Γ σ -> 𝒞 (A::Γ) (su t::σ) := by
    intro h1 h2
    simp only [𝒞] at *
    intro i T h3
    cases i
    case _ =>
      simp at *
      subst h3
      apply h1
    case _ n =>
      simp
      replace h2 := h2 n
      simp at h3
      apply h2 T h3

  theorem re : 𝒞 Γ σ -> 𝒞 (A::Γ) (re x::σ) := by
    intro h1
    simp only [𝒞] at *
    intro n
    cases n
    case _ =>
      simp
      replace h1 := h1 0
      simp at h1
      simp only [ℰ]
      apply ℒ.lift
      case _ =>
        intro h3
        simp only [ℛ]
        cases h3
      case _ =>
        intro h3
        cases h3
      case _ =>
        intro t'
        intro h3
        cases h3
    case _ n =>
      simp
      replace h1 := h1 n; apply h1

  def rename {σ : Subst Term} (r : Ren) : 𝒞 Γ σ -> 𝒞 Γ (σ ∘ r.to) := by
    intro h1
    simp only [𝒞, ℰ] at *
    intro n
    replace h1 := h1 n
    intro T h2
    have lem := ℒ.rename (A := ⟦ T ⟧) (t := (σ n)) r
    simp at lem
    apply lem
    apply h1
    apply h2

  def weaken : 𝒞 Γ σ -> 𝒞 Γ (σ ∘ +1) := rename _

  theorem lift : 𝒞 Γ σ -> 𝒞 (A::Γ) (.re 0::σ ∘ +1) := by
    intro h1
    apply re
    apply weaken (Γ := Γ) h1

end 𝒞

namespace ℰ

  theorem ind2 {P : Term -> Term -> Prop} :
    (∀ s t,
      ℰ A s ->
      ℰ B t ->
      (∀ s', s ~> s' -> P s' t) ->
      (∀ t', t ~> t' -> P s t') ->
      P s t) ->
    ℰ A s ->
    ℰ B t ->
    P s t := by
    intro h j1 j2
    induction j1 generalizing t
    case _ s' q1 q2 q3 qih =>
      induction j2
      case _ t'' j3 j4 j5 ih2 =>
        apply h
        case _ =>
          apply ℒ.lift
          case _ =>
            intro w
            replace q1 := q1 w
            apply q1
          case _ =>
            exact q2
          case _ =>
            intro w
            intro w2
            apply q3; apply w2
        case _ =>
          apply ℒ.lift
          case _ =>
            intro w1
            replace j3 := j3 w1; apply j3
          case _ =>
            exact j4
          case _ =>
            intro t'''
            exact j5
        case _ =>
          intro s'' r
          apply qih r
          apply ℒ.lift j3 j4
          exact j5
        case _ =>
          intro a
          replace ih2 := @ih2 a; intro w; replace ih2 := ih2 w; apply ih2

  theorem ind3 {P : Term -> Term -> Term -> Prop} :
    (∀ s t u,
      ℰ A s ->
      ℰ B t ->
      ℰ C u ->
      (∀ s', s ~> s' -> P s' t u) ->
      (∀ t', t ~> t' -> P s t' u) ->
      (∀ u', u ~> u' -> P s t u') ->
      P s t u) ->
    ℰ A s ->
    ℰ B t ->
    ℰ C u ->
    P s t u
  := by
  intro m j1 j2 j3
  induction j1 generalizing t u
  case _ s' h1 h2 h3 ih1 =>
    induction j2 generalizing u
    case _ t' h4 h5 h6 ih2 =>
      induction j3
      case _ u' h7 h8 h9 ih3 =>
        apply m
        case _ =>
          apply ℒ.lift; exact h1; exact h2; exact h3
        case _ =>
          apply ℒ.lift; exact h4; exact h5; exact h6
        case _ =>
          apply ℒ.lift; exact h7; exact h8; exact h9
        case _ =>
          intro s'' r
          apply ih1 r
          case _ =>
            apply ℒ.lift h4 h5 h6
          case _ =>
            apply ℒ.lift h7 h8 h9
        case _ =>
          intro t'' r
          apply ih2 r
          apply ℒ.lift h7 h8 h9
        case _ =>
          intro u'' r
          apply ih3 r

  theorem app_inv :
  (f:@ a) ~> t ->
    (∃ A b, (f = :λ[A] b) ∧ t = b[su a::+0])
    ∨ (∃ f', t = f':@ a ∧ f ~> f')
    ∨ (∃ a', t = f :@ a' ∧ a ~> a')
  := by
  intro h1
  cases h1
  case _ A' b' =>
    apply Or.inl
    exists A'; exists b'
  case _ f' h1 =>
    apply Or.inr
    apply Or.inl
    exists f'
  case _ a' h =>
    apply Or.inr
    apply Or.inr
    exists a'

  theorem app :
    ℰ (A -t> B) f ->
    ℰ A a ->
    ℰ B (f :@ a)
  := by
    intro j1 j2
    apply ind2 _ j1 j2
    intro s t h1 h2 ih1 ih2
    apply ℒ.lift
    case _ =>
      simp
    case _ =>
      intro h3
      cases h3
    case _ =>
      intro t' w1
      have lem := app_inv w1
      rcases lem with ⟨A', b, e3⟩
      case _ =>
        rcases e3 with ⟨e4, e5⟩
        subst e4 e5
        cases h1
        case _ h1 h3 h4 =>
          simp only [ℛ] at h1
          simp at h1
          apply h1
          simp only [ℰ] at h2
          apply h2
      case _ h3 =>
        rcases h3 with ⟨f', e1, e2⟩
        case _ =>
          subst e1
          apply ih1
          apply e2
        case _ h3 =>
          rcases h3 with ⟨a', e1, e2⟩
          subst e1
          apply ih2
          apply e2

  theorem nrec_inv :
    .nrec A z s n ~> t ->
    ((n = .zero ∧ .nrec A z s n ~> z) ∨
     (∃ n', n = (.succ n') ∧ t = (s :@ (.nrec A z s n'))) ∨
     (∃ z', t = .nrec A z' s n ∧ z ~> z') ∨
     (∃ s', t = .nrec A z s' n ∧ s ~> s') ∨
     (∃ n', t = .nrec A z s n' ∧ n ~> n'))
  := by
    intro h
    cases h
    case _ =>
      apply Or.inl
      apply And.intro
      case _ => rfl
      case _ => apply Red.nrec_zero
    case _ n =>
      apply Or.inr
      apply Or.inl
      apply Exists.intro n
      apply And.intro; rfl; rfl
    case _ z' r =>
      apply Or.inr
      apply Or.inr
      apply Or.inl
      apply Exists.intro z'; apply And.intro; rfl; apply r
    case _ s' r =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      apply Exists.intro s'; apply And.intro; rfl; apply r
    case _ n' r =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Exists.intro n'; apply And.intro; rfl; apply r

  theorem nrec_succ : ℰ A z -> ℰ (A -t> A) s -> ℰ A (.nrec A z s n) -> ℰ A (.nrec A z s n.succ) := by
    intro h1 h2 h3
    generalize wdef : Term.nrec A z s n = w at h3
    apply ind3 (P := λ z s n => ℰ A (Term.nrec A z s n))
    intro z' s' n' j1 j2 j3 ih1 ih2 ih3
    apply ℒ.lift sorry sorry
    intro t' r
    cases r



  theorem nrec_value :
    ℰ A z ->
    ℰ (A -t> A) s ->
    NatLike n ->
    ℰ A (.nrec A z s n)
  := by
    intro j1 j2 j3
    induction j3
    case _ =>
      apply ind2 _ j1 j2
      intro z' s' h1 h2 h3 h4
      apply ℒ.lift
      case _ =>
        intro w1; cases w1
      case _ =>
        intro w1; cases w1
      case _ =>
        intro t' w1
        cases w1
        case _ =>
          apply h1
        case _ z'' r =>
          apply h3; apply r
        case _ s'' r =>
          apply h4; apply r
        case _ n' r =>
          cases r
    case _ n' j3 ih1 =>
      apply ℒ.lift sorry sorry
      intro t' h1
      cases h1

      -- apply ind2 _ j1 j2
      -- case _ =>
      --   intro z' s' h1 h2 h3 h4
      --   apply ℒ.lift
      --   case _ =>
      --     sorry
      --   case _ =>
      --     sorry
      --   case _ =>
      --     intro t' w1
      --     cases w1
      --     case _ =>
      --       cases ih1

      --       sorry



  theorem nrec :
    ℰ A z ->
    ℰ (A -t> A) s ->
    ℰ Ty.nat n ->
    ℰ A (.nrec A z s n)
  := by
    intro j1 j2 j3
    induction j3
    case _ t h1 h2 ih1 =>
      apply ℒ.lift
      case _ =>
        sorry
      case _ =>
        intro t' r
        cases r
        case _ =>
          apply j1
        case _ n' =>
          have lem := progress n'
          cases lem
          case _ =>
            sorry
          case _ h =>
            obtain ⟨n'', r⟩ := h
            replace r := Red.succ r
            replace ih1 := ih1 r
            simp at ih1
            apply ℒ.preservation ih1
            sorry
          all_goals sorry
        all_goals sorry
    -- apply ind3 _ j1 j2 j3
    -- intro s t u h1 h2 h3 ih1 ih2 ih3
    -- apply ℒ.lift
    -- case _ =>
    --   intro h; simp at h
    -- case _ =>
    --   intro t' r
    --   have lem := nrec_inv r
    --   cases lem
    --   case _ h =>
    --     rcases h with ⟨e1, e2⟩
    --     subst e1
    --     cases r
    --     case _ =>
    --       apply h1
    --     case _ h =>
    --       apply ih1
    --       apply h
    --     case _ h =>
    --       apply ih2
    --       apply h
    --     case _ h =>
    --       apply ih3
    --       apply h
    --   case _ h =>
    --     cases h
    --     case _ h =>
    --       rcases h with ⟨u', e1, e2⟩
    --       subst e1 e2
    --       cases h3
    --       case _ q1 q2 =>

    --         sorry
    --     case _ h =>
    --       cases h
    --       case _ =>
    --         sorry
    --       case _ =>
    --         sorry

  theorem lam : SN Red b -> ℛ (⟦ (A -t> B) ⟧) (:λ[C] b) -> ℰ (A -t> B) (:λ[C] b) := by
    intro h1 h2
    induction h1
    case _  x j1 ih =>
      apply ℒ.lift
      case _ =>
        intro w1
        apply h2
      case _ =>
        intro t' w1
        cases w1
        case _ t' w1 =>
          apply ih
          case _ =>
            apply w1
          case _ =>
            simp only [ℛ] at *
            simp
            intro r a w2
            have w3 : x[su a::r] ~> t'[su a::r] := Red.subst _ w1
            apply ℒ.preservation _ w3
            simp at h2
            apply h2
            apply w2

  theorem succ : ℰ Ty.nat n -> ℰ Ty.nat n.succ := by
    intro h
    induction h; case _ t j1 j2 ih =>
    apply ℒ.lift; intro r; simp at r
    intro t' r
    cases r
    case _ n' r =>
      apply ih; apply r

end ℰ

theorem fundamental : Γ ⊢ t : A -> Γ ⊨ t : A := by
  intro j
  induction j
  case _  Γ' T n h1 =>
    simp
    intro σ h2
    simp only [𝒞] at h2
    replace h2 := h2 n
    apply h2
    apply h1
  case _ Γ' A' B f a h1 h2 ih1 ih2 =>
    simp
    intro σ j1
    simp at ih1 ih2
    apply ℒ.lift
    case _ =>
      intro w1
      simp at w1
    case _ =>
      intro t' w1
      replace ih1 := ih1 σ j1
      replace ih2 := ih2 σ j1
      apply ℒ.preservation _ w1
      apply ℰ.app ih1 ih2
  case _ Γ' A' B t' h1 ih =>
    simp at *
    intro σ j1
    apply ℰ.lam
    case _ =>
      apply ℒ.sound (A := ⟦ B ⟧)
      apply ih
      apply 𝒞.lift
      apply j1
    case _ =>
      simp only [ℛ]
      intro r
      simp
      intro a w1
      apply ih
      apply 𝒞.term_su
      case _ =>
        apply w1
      case _ =>
        apply 𝒞.rename
        apply j1
  case _ =>
    simp at *
    intro σ j
    apply ℒ.lift; intro h; simp at h; intro t' h; cases h
  case _ Γ n j ih =>
    simp at *
    intro σ h
    apply ℰ.succ; apply ih; apply h
  case _ Γ z A s n h1 h2 h3 ih1 ih2 ih3 =>
    simp at *
    intro σ j
    apply ℒ.lift
    case _ => intro h; simp at h
    case _ =>
      intro t' r
      apply ℒ.preservation _ r
      apply ℰ.nrec; apply ih1; apply j; apply ih2; apply j; apply ih3; apply j

theorem strong_normalization : Γ ⊢ t : A -> SN Red t := by
  intro h1
  have lem : Γ ⊨ t : A := by apply fundamental h1
  simp at lem
  replace lem := lem +0
  simp [𝒞] at lem
  simp [ℰ] at lem
  apply ℒ.sound
  case _ =>
    apply lem
    intro i T j1
    apply ℒ.var
