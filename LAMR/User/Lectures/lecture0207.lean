import LAMR

/-
Comments on assignment 3:

When you define an inductive type, add `deriving Repr` so that an #eval can display it.

  https://avigad.github.io/lamr/using_lean_as_a_programming_language.html#inductive-data-types-in-lean

Recall the semantic definitions:

https://avigad.github.io/lamr/propositional_logic.html#semantics

It's tempting to write

  ⟦A ∧ B⟧_τ = ⟦A⟧_τ ∧ ⟦B⟧_τ

but that is not good notation; the two ∧'s are different. You might say

  ⟦A ∧ B⟧_τ = boolean_and(⟦A⟧_τ, ⟦B⟧_τ)

where boolean_and is the relevant function on {⊤, ⊥}, or

  ⟦A ∧ B⟧_τ = the boolean conjunction of ⟦A⟧_τ and ⟦B⟧_τ,

or work around it with the following fact:

  ⟦A ∧ B⟧_τ = ⊤ if and only if ⟦A⟧_τ = ⊤ and ⟦B⟧_τ = ⊤.

(Logicians tend to favor the last.)

Also: you can generally get away with handling one binary
connective and saying that the others are "similar."
-/

/-
Note: update the LAMR repository. From the terminal:

  git pull
  lake build

Overview:

- Resolution proof in Lean
- The Tseitin encoding in Lean

(Marijn on SAT solvers and how to use them)

- Encodings in Lean

-/

/-
Resolution proof in Lean
-/

namespace Resolution

/--
The resolution Step.

C ∨ p
D ∨ ¬ p

C ∨ D
-/
def resolve (c₁ c₂ : Clause) (var : String) : Clause :=
  (c₁.erase (Lit.pos var)).union' (c₂.erase (Lit.neg var))

/--
A line of a resolution proof is either a hypothesis or the result of a
resolution step.
-/
inductive Step where
  | hyp (clause : Clause) : Step
  | res (var : String) (pos neg : Nat) : Step
deriving Inhabited, Repr

def Proof := Array Step deriving Inhabited, Repr

-- Ignore this: it is boilerplate to make the `p[i]` notation work.
instance : GetElem Proof Nat Step (fun xs i => i < xs.size) :=
  inferInstanceAs (GetElem (Array Step) _ _ _)

-- determines whether a proof is well-formed
def Proof.wellFormed (p : Proof) : Bool := Id.run do
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp _ => continue
      | Step.res _ pos neg =>
          if i ≤ pos ∨ i ≤ neg then
            return false
  true

-- prints out the proof
def Proof.show (p : Proof) : IO Unit := do
  if ¬ p.wellFormed then
    IO.println "Proof is not well-formed."
    return
  let mut clauses : Array Clause := #[]
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp c =>
          clauses := clauses.push c
          IO.println s!"{i}: hypothesis: {c}"
      | Step.res var pos neg =>
          let resolvent := resolve clauses[pos]! clauses[neg]! var
          clauses := clauses.push resolvent
          IO.println s!"{i}: resolve {pos}, {neg} on {var}: {resolvent}"

end Resolution

section
open Resolution

def example0 : Proof := #[
  .hyp clause!{-p -q r},
  .hyp clause!{-r},
  .hyp clause!{p -q},
  .hyp clause!{-s q},
  .hyp clause!{s},
  .res "r" 0 1,
  .res "s" 4 3,
  .res "q" 6 2,
  .res "p" 7 5,
  .res "q" 6 8
]

#eval example0.wellFormed
#eval example0.show

def example1 : Proof := #[
  .hyp clause!{p q},
  .hyp clause!{-p},
  .hyp clause!{-q},
  .res "p" 0 1,
  .res "q" 3 2
]

#eval example1.wellFormed
#eval example1.show

def example2 : Proof := #[
  .hyp clause!{p q r},
  .hyp clause!{-p s},
  .hyp clause!{-q s},
  .hyp clause!{-r s},
  .hyp clause!{-s},
  .res "p" 0 1,
  .res "q" 5 2,
  .res "r" 6 3,
  .res "s" 7 4
]

#eval example2.wellFormed
#eval example2.show

-- Homework: Finish this to get a proof of ⊥.
def example3 : Proof := #[
  .hyp clause!{p q -r},
  .hyp clause!{-p -q r},
  .hyp clause!{q r -s},
  .hyp clause!{-q -r s},
  .hyp clause!{p r s},
  .hyp clause!{-p -r -s},
  .hyp clause!{-p q s},
  .hyp clause!{p -q -s}
]

#eval example3.wellFormed
#eval example3.show

end

/-
Encoding formulas for SAT solvers.

- Graph coloring
- Sudoku (hard to understand)

Homework:

Monochromatic rectangles

Challenges:

- You need to use CaDiCaL.
  - On Linux, it should just work.
  - On Mac or Windows, you can go to the CaDiCaL repository and follow
    the build instructions, and then put the binary in `LAMR/bin`.
  - On any platform, you can use Codespaces or Gitpod.

- File IO and standard IO require the "IO Monad". We haven't explained
  that or how to use it, but we will provide code templates so that
  you can focus on encoding and decoding.

- Encoding and decoding require array operations,
  parsing strings like "x_3_4_5" to [3,4,5], etc.
-/

def bar (x : Nat) : Except String Nat :=
  if x = 5 then .ok 3 else .error "not five!"

#eval bar 4

def test : IO Unit := do
  let mut s : Array (Array Nat) := mkArray 3 (mkArray 3 0)
  s := s.set! 1 (s[1].set! 2 3)
  s := s.set! 0 (s[0].set! 1 1)
  for i in [:3] do
    for j in [:3] do
      IO.print s!" {s[i]![j]!} "
    IO.println ""
  return ()

#eval test

#check Array.modify

-- This is version is more efficient: it does not copy the row before modifying it.

def test' : IO Unit := do
  let mut s : Array (Array Nat) := mkArray 3 (mkArray 3 0)
  s := s.modify 1 (fun row => row.set! 2 3)
  s := s.modify 0 (fun row => row.set! 1 1)
  for i in [:3] do
    for j in [:3] do
      IO.print s!" {s[i]![j]!} "
    IO.println ""
  return ()

#eval test'

def myCnf : CnfForm :=
  cnf!{ x_0_1 x_1_0, -x_0_0 -x_1_1 }

def test2 : IO Unit := do
  let (_, result) ← callCadical myCnf
  match result with
    | SatResult.Unsat _ => IO.println "Sudoku unsat."
    | SatResult.Sat τ  => IO.println τ

#eval test2

#eval "x_3_22".splitOn "_"

def foo : Except String (List Nat) := Id.run do
  match "x_3_22".splitOn "_" with
    | [_, i, j] =>
      match [i.toNat?, j.toNat?] with
        | [some i, some j] => .ok [i, j]
        | _ => .error "failed!"
    | _ => .error "too bad"

#eval foo

def foo' : Except String (List Nat) := Id.run do
  match "x_3_22".splitOn "_" |>.map String.toNat? with
    | [_, some i, some j] => .ok [i, j]
    | _ => .error "too bad"

#eval foo'
