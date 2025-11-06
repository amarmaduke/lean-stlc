import LeanStlc

def bool_ty (A : Ty) : Ty := A -t> A -t> A

def tt (A : Ty) : Term := :λ[A] :λ[A] #1
def ff (A : Ty) : Term := :λ[A] :λ[A] #0
def not (A : Ty) : Term := :λ[bool_ty (bool_ty A)] #0 :@ (ff A) :@ (tt A)

#eval Option.get! (infer [] (tt ⊤))
#eval Option.get! (infer [] (not ⊤))
#eval Option.get! (infer [] ((not ⊤) :@ (tt (bool_ty ⊤))))

def main : IO Unit := do return ()
