import LAMR

/-
# Implementing the syntax of Propositional Logic

The textbook definitions are here:
https://avigad.github.io/lamr/propositional_logic.html#syntax
-/

namespace hidden

inductive PropForm
  | tr     : PropForm
  | fls    : PropForm
  | var    : String → PropForm
  | conj   : PropForm → PropForm → PropForm
  | disj   : PropForm → PropForm → PropForm
  | impl   : PropForm → PropForm → PropForm
  | neg    : PropForm → PropForm
  | biImpl : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq, Inhabited

end hidden

#print PropForm

#check (PropForm.neg (PropForm.var "x"))

#check (PropForm.impl (PropForm.conj (PropForm.var "p") (PropForm.var "q")) (PropForm.var "r"))

section
open PropForm

#check (impl (conj (var "p") (var "q")) (var "r"))

end

def foo : PropForm := .impl (.conj (.var "p") (.var "q")) (.var "r")

#check (.impl (.conj (.var "p") (.var "q")) (.var "r") : PropForm)

#check prop!{p ∧ q → (r ∨ ¬ p) → q}
#check prop!{p ∧ q ∧ r → p}

def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2}

#print propExample
#eval propExample

#eval toString propExample


/-
Some examples of structural recursion.
-/

namespace PropForm

def complexity : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => complexity A + 1
  | conj A B => complexity A + complexity B + 1
  | disj A B => complexity A + complexity B + 1
  | impl A B => complexity A + complexity B + 1
  | biImpl A B => complexity A + complexity B + 1

def depth : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => depth A + 1
  | conj A B => max (depth A) (depth B) + 1
  | disj A B => max (depth A) (depth B) + 1
  | impl A B => max (depth A) (depth B) + 1
  | biImpl A B => max (depth A) (depth B) + 1

def vars : PropForm → List String
  | .var x => [x]
  | .tr => []
  | .fls => []
  | .neg A => vars A
  | .conj A B => (vars A).union' (vars B)
  | .disj A B => (vars A).union' (vars B)
  | .impl A B => (vars A).union' (vars B)
  | .biImpl A B => (vars A).union' (vars B)

/-
def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2}
-/

#eval complexity propExample
#eval depth propExample
#eval vars propExample

end PropForm

#eval PropForm.complexity propExample
#eval propExample.complexity

#check PropAssignment
#print PropAssignment

#check PropAssignment.eval

def PropForm.eval (v : PropAssignment) : PropForm → Bool
  | var s => v.eval s   -- fix this!!
  | tr => true
  | fls => false
  | neg A => !(eval v A)
  | conj A B => (eval v A) && (eval v B)
  | disj A B => (eval v A) || (eval v B)
  | impl A B => !(eval v A) || (eval v B)
  | biImpl A B => (!(eval v A) || (eval v B)) && (!(eval v B) || (eval v A))

/-
def propExample := prop!{(p ∧ q) → (((r ∧ p) ∨ ¬ s1) → s2)}
-/

#eval let v := PropAssignment.mk [("p", true), ("q", true), ("r", true)]
      propExample.eval v

#check propassign!{p, q, r}

#eval propExample.eval propassign!{p, q, r}

def allSublists : List α → List (List α)
  | [] => [[]]
  | a :: as =>
      let recval := allSublists as
      recval.map (a :: .) ++ recval

#eval allSublists propExample.vars

def truthTable (A : PropForm) : List (List Bool × Bool) :=
  let vars := A.vars
  let assignments := (allSublists vars).map (fun l => PropAssignment.mk (l.map (., true)))
  let evalLine := fun v : PropAssignment => (vars.map v.eval, A.eval v)
  assignments.map evalLine

#eval propExample.vars
#eval truthTable propExample

def PropForm.isValid (A : PropForm) : Bool := (truthTable A).all Prod.snd
def PropForm.isSat(A : PropForm) : Bool := (truthTable A).any Prod.snd

#eval propExample.isValid
#eval propExample.isSat
#eval prop!{(p ∨ ¬ p)}.isValid

namespace hidden

inductive Lit
  | tr  : Lit
  | fls : Lit
  | pos : String → Lit
  | neg : String → Lit

inductive NnfForm :=
  | lit  (l : Lit)       : NnfForm
  | conj (p q : NnfForm) : NnfForm
  | disj (p q : NnfForm) : NnfForm

/-
p ∧ (¬ q ∨ (r ∧ s))

¬ (p ∧ (¬ q ∨ (r ∧ s)))

¬ p ∨ (q ∧ (¬ r ∨ ¬ s))

-/

def Lit.negate : Lit → Lit
  | tr   => fls
  | fls  => tr
  | pos s => neg s
  | neg s => pos s

def NnfForm.neg : NnfForm → NnfForm
  | lit l    => lit l.negate
  | conj p q => disj (neg p) (neg q)
  | disj p q => conj (neg p) (neg q)

namespace PropForm

def toNnfForm : PropForm → NnfForm
  | tr         => NnfForm.lit Lit.tr
  | fls        => NnfForm.lit Lit.fls
  | var p      => NnfForm.lit (Lit.pos p)
  | neg A      => A.toNnfForm.neg
  | conj p q   => NnfForm.conj p.toNnfForm q.toNnfForm
  | disj p q   => NnfForm.disj p.toNnfForm q.toNnfForm
  | impl p q   => NnfForm.disj p.toNnfForm.neg q.toNnfForm
  | biImpl p q => NnfForm.conj (NnfForm.disj p.toNnfForm.neg q.toNnfForm)
                               (NnfForm.disj q.toNnfForm.neg p.toNnfForm)

end PropForm

#check nnf!{p ∧ q ∧ ((r ∧ ¬ q) ∨ ¬ p) ∨ q}

end hidden

def propExample0 := prop!{p ∧ q → (r ∨ ¬ p) → q}
def propExample1 := prop!{p ∧ q ∧ r → p}
def propExample2 := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2 }

#eval propExample0.toNnfForm
#eval propExample.toNnfForm
#eval toString propExample.toNnfForm

namespace hidden₂

def Clause := List Lit

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

#eval propExample.toCnfForm

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2)}.toCnfForm.toString

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2) ∨ (r1 ∧ r2) ∨ (s1 ∧ s2)}.toCnfForm.toString

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

#eval propExample0.toCnfForm'

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2)}.toCnfForm'.toString

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2) ∨ (r1 ∧ r2) ∨ (s1 ∧ s2)}.toCnfForm.toString
