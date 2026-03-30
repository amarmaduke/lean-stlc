import LeanSubst
import LeanStlc.Reduction
import LeanStlc.Typing

open LeanSubst

def Typing.preservation_step : Γ ⊢ t : A -> t ~> t' -> Γ ⊢ t' : A
| app (lam t) a, .beta => beta t a
| app f a, .app1 r => app (f.preservation_step r) a
| app f a, .app2 r => app f (a.preservation_step r)
| lam t, .lam r => lam (t.preservation_step r)
| succ t, .succ r => succ (t.preservation_step r)
| nrec z s n, .nrec_zero => z
| nrec z s (succ n), .nrec_succ => app s (nrec z s n)
| nrec z s n, .nrec1 r => nrec (z.preservation_step r) s n
| nrec z s n, .nrec2 r => nrec z (s.preservation_step r) n
| nrec z s n, .nrec3 r => nrec z s (n.preservation_step r)

def Typing.preservation (j : Γ ⊢ t : A) : t ~>* t' -> Γ ⊢ t' : A
| .refl => j
| .step r1 r2 => (preservation j r1).preservation_step r2
