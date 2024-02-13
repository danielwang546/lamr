import LAMR

namespace hidden₂

def Clause : Type := List Lit

def CnfForm := List Clause

end hidden₂

#print Lit
#print Clause
#print CnfForm

def exLit0 := lit!{ p }
def exLit1 := lit!{ -q }

#print exLit0
#print exLit1

def exClause0 := clause!{ p }
def exClause1 := clause!{ p -q r }
def exClause2 := clause!{ r -s }

#print exClause0
#print exClause1
#print exClause2

def exCnf0 := cnf!{
  p,
  -p q -r,
  -p q
}

def exCnf1 := cnf!{
  p -q,
  p q,
  -p -r,
  -p r
}

def exCnf2 := cnf!{
  p q,
  -p,
  -q
}

#print exCnf0
#print exCnf1
#print exCnf2

#eval toString exClause1
#eval toString exCnf2

#eval List.insert lit!{ r } exClause0

#eval exClause0.insert lit!{r}

#eval exCnf0 ++ exCnf1

#eval exClause0.union' exClause1

#eval List.Union [exClause0, exClause1, exClause2]

#eval exCnf1.map exClause0.union'

namespace hidden₃

def CnfForm.disj (cnf1 cnf2 : CnfForm) : CnfForm :=
(cnf1.map (fun cls => cnf2.map cls.union')).Union

#eval cnf!{p, q, u -v}.disj cnf!{r1 r2, s1 s2, t1 t2 t3}
#eval toString $ cnf!{p, q, u -v}.disj cnf!{r1 r2, s1 s2, t1 t2 t3}

def NnfForm.toCnfForm : NnfForm → CnfForm
  | NnfForm.lit (Lit.pos s) => [ [Lit.pos s] ]
  | NnfForm.lit (Lit.neg s) => [ [Lit.neg s] ]
  | NnfForm.lit Lit.tr      => []
  | NnfForm.lit Lit.fls     => [ [] ]
  | NnfForm.conj A B        => A.toCnfForm.conj B.toCnfForm
  | NnfForm.disj A B        => A.toCnfForm.disj B.toCnfForm

def PropForm.toCnfForm (A : PropForm) : CnfForm := A.toNnfForm.toCnfForm

end hidden₃

def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2}

#eval propExample.toCnfForm

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2)}.toCnfForm.toString

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2) ∨ (r1 ∧ r2) ∨ (s1 ∧ s2)}.toCnfForm.toString

/-
(c₁ ∧ c₂ ∧ ... ∧ c_n) ∨ (d₁ ∧ d₂ ∧ ... ∧ d_m)

c₁ ∨ (d₁ ∧ d₂ ∧ ... ∧ d_m)

-/

def disjClauseCnf : Clause → CnfForm → CnfForm
  | _, []    => []
  | c, d::ds => c.union' d :: disjClauseCnf c ds

def disjClauseCnf' (cls : Clause) (cnf2 : CnfForm) : CnfForm :=
cnf2.map cls.union'

def CnfForm.disj0 : CnfForm → CnfForm → CnfForm
  | [], _       => []
  | c :: cs, ds => (disjClauseCnf c ds).union' (CnfForm.disj0 cs ds)

def CnfForm.disj1 (cnf1 cnf2 : CnfForm) : CnfForm :=
(cnf1.map (fun cls => cnf2.map cls.union')).Union

def CnfForm.disj2 (cnf1 cnf2 : CnfForm) : CnfForm :=
cnf1.foldr
  (fun c ds => (disjClauseCnf c cnf2).union' ds)
  []

def CnfForm.disj3 (cnf1 cnf2 : CnfForm) : CnfForm :=
cnf1.foldr
  (fun c ds => (cnf2.map c.union').union' ds)
  []

def CnfForm.disj' (cnf1 cnf2 : CnfForm) : CnfForm :=
cnf1.foldr (fun c => cnf2.map c.union' |>.union') []

def CnfForm.disj4 (cnf1 cnf2 : CnfForm) : CnfForm := Id.run do
  let mut out : CnfForm := []
  for c₁ in cnf1 do
    for c₂ in cnf2 do
      out := List.insert (c₁.union' c₂) out
  return out

#eval cnf!{p, q, u -v}.disj cnf!{r1 r2, s1 s2, t1 t2 t3}
#eval toString $ cnf!{p, q, u -v}.disj cnf!{r1 r2, s1 s2, t1 t2 t3}

def NnfForm.toCnfForm' : NnfForm → CnfForm
  | NnfForm.lit (Lit.pos s) => [ [Lit.pos s] ]
  | NnfForm.lit (Lit.neg s) => [ [Lit.neg s] ]
  | NnfForm.lit Lit.tr      => []
  | NnfForm.lit Lit.fls     => [ [] ]
  | NnfForm.conj A B        => A.toCnfForm'.conj B.toCnfForm'
  | NnfForm.disj A B        => A.toCnfForm'.disj B.toCnfForm'

def PropForm.toCnfForm' (A : PropForm) : CnfForm := A.toNnfForm.toCnfForm

#eval propExample.toCnfForm'

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2)}.toCnfForm'.toString

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2) ∨ (r1 ∧ r2) ∨ (s1 ∧ s2)}.toCnfForm.toString
