import Std
import Mathlib.Tactic

/-
Office hours:

Alex, Mondays at 4-5pm, BH 139
Jeremy, Tuesdays at 10 am, BH 135 E
Marijn, Tuesdays, 1-2, GHC 9107
Josh, Tuesdays at 4:30-5:30pm, BH 139
Joseph, Wednesdays at 10:30-11:30am, BH 139
Tika, Wednesdays 2-3pm, BH 139

Remember:
- Textbook is online here: https://avigad.github.io/lamr
- Github repository: https://github.com/avigad/lamr
- Course website is here: https://www.cs.cmu.edu/~mheule/15311-s24/

Options:
- Use Lean in Codespaces or Gitpod (see repo)
- Install Lean and VS Code, and then use ctrl-shift-P "Lean 4: Project: Download Project ..."

Resources for using Lean:
- Lean 4 manual: https://leanprover.github.io/lean4/doc/
- Functional Programming in Lean: https://lean-lang.org/functional_programming_in_lean/
- Theorem Proving in Lean: https://leanprover.github.io/theorem_proving_in_lean/
- Lean community website: https://leanprover-community.github.io/
- Lean Zulip channel: https://leanprover.zulipchat.com/

Lean is both a programming language and a proof assistant.

It is based on a foundational system known as *dependent type theory*.

In type theory,
- everything is an expression
- every expression has a type.

The type determines what sort of object it is.

There are:
- data types, `T : Type`
- objects, `t : T`
- propositions, `P : Prop`
- proofs, `p : P`
-/

#check Nat
#check Int
#check Bool
#check List Nat
#check List (List Nat)
#check Option Nat
#check Nat → Nat
#check ℕ
#check String

#check 2 + 2
#check (2 : Int) + 2
#check [1, 2, 3]
#check some 2
#check "hello" ++ " world"
#check fun x => x + 1

def four : Nat := 2 + 2
def four' := 2 + 2
def isOne (x : Nat) : Bool := if x = 1 then true else false
def isOne' : Nat → Bool := fun x => if x = 1 then true else false

#check four
#print four

#eval 2 + 2
#eval four
#eval isOne 7
#eval isOne 1
#eval IO.println "hello world"

#check 2 + 2 = 4
#check 2 + 2 = 5

def my_silly_proposition : Prop := 2 + 2 = 4

#check ∀ n, ∀ a b c : Int, n > 2 → a^n + b^n ≠ c^n

def Fermat_statement := ∀ n, ∀ a b c : Int, n > 2 → a^n + b^n ≠ c^n

theorem silly_theorem : 2 + 2 = 4 := rfl

theorem FLT : ∀ n, ∀ a b c : Int, n > 2 → a^n + b^n ≠ c^n :=
  sorry

def foo (x : ℤ) := 3 * x^2 + 7

example : ∀ x, foo x ≥ 7 := by
  intro x
  simp [foo]
  exact sq_nonneg x

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5

def hanoi (num_disks start finish aux: Nat) : IO Unit :=
  match num_disks with
  | 0 => pure ()
  | (n + 1) => do
    hanoi n start aux finish
    IO.println s!"move disk from {start} to {finish}"
    hanoi n aux finish start

#eval hanoi 10 1 2 3

def add_nums : List Nat → Nat
  | [] => 0
  | x :: xs => x + add_nums xs

#eval add_nums [1, 2, 3, 4, 5]

#eval List.range 10

section
open List

#eval range 10
end

section
open List

#eval add_nums <| range 10

#eval map (fun x => x + 7) (range 10)
#eval map (. + 7) (range 10)

#eval (range 10).map (. + 7)

#eval foldl (fun y => . + (3 * y)) 0 (range 10)

end

namespace hidden

def reverseAux : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => reverseAux xs (x :: ys)

def reverse (xs : List α) := reverseAux xs []

#eval reverse [1, 2, 3, 4, 5]

end hidden

partial def my_gcd (x y : Nat) : Nat :=
  if y = 0 then x else my_gcd y (x % y)

#eval my_gcd 12 18

partial def bad (x : Nat)  := bad x + 1

namespace inductive_example

inductive BinTree
  | empty : BinTree
  | node : BinTree → BinTree → BinTree

#check BinTree.empty
#check @BinTree.node

open BinTree

#check empty
#check node empty empty
#check node empty (node empty empty)

def size : BinTree → Nat
  | empty => 0
  | node l r => 1 + size l + size r

#eval size <| node empty (node empty empty)

end inductive_example

def showSums : IO Unit := do
  let mut sum := 0
  for i in [:100] do
    sum := sum + i
    IO.println s!"sum up to {i} is {sum}"

#eval showSums

#check Array Int
