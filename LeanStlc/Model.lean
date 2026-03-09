import LeanSubst
import LeanStlc.Term

open LeanSubst

universe u u1 u2 u3

class Model (D : Sort u) where
  A : D -> D -> D
  P : D
  N : D

@[simp]
def Model.int_ty [Model D] : Ty -> D
| .base => P
| .arrow a b => A (int_ty a) (int_ty b)
| .nat => N

notation "⟦ " t " ⟧ " => Model.int_ty t
