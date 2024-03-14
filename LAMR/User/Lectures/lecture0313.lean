import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import LAMR

/-
Today:
- More on induction in Lean (the proof assistant).
- Implementing first-order logic in Lean (the programming language).

Apologies:
- Monday's lecture was only a quick introduction to natural deduction.
- The Curry-Howard isomorphism is more than an analogy.
  (Propositions as types, proofs as programs.)

So far we have seen (in Lean):
- propositional logic
- equality
- structural induction

This only scratches the surface! But it is already enough to do some
interesting things.
-/

/-
Defining addition.
-/

open Nat

def add' : Nat → Nat → Nat
  | m, zero => m
  | m, succ n => succ (add' m n)

theorem zero_add' (n : Nat) : add' 0 n = n := by
  induction n with
  | zero => rw [add']
  | succ n ih =>
    rw [add', ih]

theorem succ_add' (m n : Nat) : add' (succ m) n = succ (add' m n) := by
  induction n with
  | zero => rw [add', add']
  | succ n ih => rw [add', ih, add']

theorem add'_comm (m n : Nat) : add' m n = add' n m := by
  induction n with
  | zero => rw [add', zero_add']
  | succ n ih => rw [add', succ_add', ih]

/-
Induction on lists.
-/

open List

variable {α : Type}
variable (as bs cs : List α)
variable (a b c : α)

-- This is one way to define append:
def append' : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: append' xs ys

-- These follow from the addition of the append function.
#check nil_append
#check cons_append

example : [] ++ as = as := nil_append as
example : (a :: as) ++ bs = a :: (as ++ bs) := cons_append a as bs

example : [] ++ as = as := rfl
example : (a :: as) ++ bs = a :: (as ++ bs) := rfl

theorem append_nil' : as ++ [] = as := by
  induction as with
  | nil => rw [nil_append]
  | cons b bs ih => rw [cons_append, ih]

theorem append_assoc' : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rw [nil_append, nil_append]
  | cons a as ih => rw [cons_append, cons_append, cons_append, ih]

-- In fact: Lean defines a more efficient, tail-recursive version and proves it equal
-- to the definition above.

-- This is how `map` is defined.
def map' (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map' f xs

-- You can use `rw [map]` to exapnd the definition.

theorem map_append (f : α → β) (xs ys : List α) :
    map f (xs ++ ys) = map f xs ++ map f ys := by
  sorry

theorem map_map (f : α → β) (g : β → γ) (xs : List α) : map g (map f xs) = map (g ∘ f) xs := by
  induction xs with
  | nil =>
    rw [map, map, map]
  | cons x xs ih =>
    rw [map, map, map, ih]
    rfl

example (f : α → β) (g : β → γ) (xs : List α) : map' g (map' f xs) = map' (g ∘ f) xs := by
  induction xs <;> simp [map', *]

/-
Induction on propositional formulas.
-/

namespace PropForm

def Occurs (v : String) : PropForm → Prop
  | tr => False
  | fls => False
  | var w => v = w
  | neg A => Occurs v A
  | conj A B => Occurs v A ∨ Occurs v B
  | disj A B => Occurs v A ∨ Occurs v B
  | impl A B => Occurs v A ∨ Occurs v B
  | biImpl A B => Occurs v A ∨ Occurs v B

def eval (v : String → Bool) : PropForm → Bool
  | var s => v s
  | tr => true
  | fls => false
  | neg A => !(eval v A)
  | conj A B => (eval v A) && (eval v B)
  | disj A B => (eval v A) || (eval v B)
  | impl A B => !(eval v A) || (eval v B)
  | biImpl A B => (!(eval v A) || (eval v B)) && (!(eval v B) || (eval v A))

variable (A B : PropForm) (τ : String → Bool) (v : String)

theorem eval_of_not_occurs (h : ¬ Occurs v A) (b : Bool) :
    A.eval (fun w => if v = w then b else τ w) = A.eval τ := by
  induction A with
  | var s =>
    rw [eval, eval]
    rw [Occurs] at h
    rw [if_neg h]
  | tr =>
    rw [eval, eval]
  | fls =>
    sorry
  | neg A ihA =>
    sorry
  | conj A B ihA ihB =>
    sorry
  | disj A B ihA ihB =>
    sorry
  | impl A B ihA ihB =>
    sorry
  | biImpl A B ihA ihB =>
    sorry

example (h : ¬ Occurs v A) (b : Bool) :
    A.eval (fun w => if v = w then b else τ w) = A.eval τ := by
  induction A <;> simp [*, Occurs, eval, not_or] at * <;> simp [*] at *

end PropForm

/-
Back to FOL
-/

-- Remember the syntax of FOL: https://www.cs.cmu.edu/~mheule/15311-s24/slides/FOL.pdf

#check FOTerm
#check FOForm

section
open FOTerm

#check var "x"
-- f(x, g(y))
#check app "f" [var "x", app "g" [var "y"]]

end

def ex1 := term!{ %x }
def ex2 := term!{ c }
def ex3 := term!{ f(f(a, %x), f(g(c, f(%y, d)), b)) }

#print ex1
#print ex2
#print ex3

#eval ex1
#eval ex2
#eval ex3

def assign1 : FOAssignment Nat := assign!{x ↦ 3, y ↦ 5, z ↦ 2}

/-
Substitution uses a term assignment.
-/

#eval ex3.subst assign!{x ↦ term!{h(a)}, y ↦ term!{f(a, h(a), d)}}

/-
First-order formulas
-/

#check fo!{ r(x, y) ∧ r(x, z) → p(z) ∨ ⊤ }
#check fo!{ ∀ x. ∃ y. r (x, y) ∨ p(x) }

#eval fo!{ r(x, y) ∧ r(x, z) → p(z) ∨ ⊤ }
#eval fo!{ ∀ x. ∃ y. r (x, y) ∨ p(x) }

/-
Interpreting functions.
-/

def FnInterp α := FOAssignment (List α → α)

instance [Inhabited α] : Coe (Std.AssocList String (List α → α)) (FnInterp α) :=
⟨fun l => l.getA⟩

/- examples -/

def arithFnInterp : FnInterp Nat
  | "plus"  => fun l => l.getA 0 + l.getA 1
  | "times" => fun l => l.getA 0 * l.getA 1
  | "zero"  => fun _ => 0
  | "one"   => fun _ => 1
  | "two"   => fun _ => 2
  | "three" => fun _ => 3
  | _       => fun _ => default

def arithFnInterp' : FnInterp Nat :=
assign!{
  plus ↦ fun l : List Nat => l.getA 0 + l.getA 1,
  times ↦ fun l => l.getA 0 * l.getA 1,
  zero ↦ fun _ => 0,
  one ↦ fun _ => 1,
  two ↦ fun _ => 2,
  three ↦ fun _ => 3 }

namespace FOTerm

partial def eval {α} [Inhabited α] (fn : FnInterp α) (σ : FOAssignment α) : FOTerm → α
  | var x   => σ x
  | app f l => fn f (l.map (eval fn σ))
end FOTerm

/- examples -/

def arith_ex1 := term!{ plus(times(%x, two), plus(%y, three)) }

#eval arith_ex1.eval arithFnInterp assign!{ x ↦ 3, y ↦ 5 }
#eval arith_ex1.eval arithFnInterp assign!{ x ↦ 7, y ↦ 11 }

/-
Substitution and evaluation
-/

def arith_ex2 := term!{ plus(one, times(three, %z))}
def arith_ex3 := term!{ plus(%z, two) }

-- these two should give the same result!

#eval (arith_ex1.subst
        assign!{ x ↦ arith_ex2, y ↦ arith_ex3 }).eval
        arithFnInterp assign!{z ↦ 7}

#eval arith_ex1.eval arithFnInterp
  assign!{ x ↦ (arith_ex2.eval arithFnInterp assign!{z ↦ 7}),
           y ↦ (arith_ex3.eval arithFnInterp assign!{z ↦ 7}) }

/-
Another view on substitution: evaluation in the term FnInterp.
-/

def TermFnInterp : FnInterp FOTerm := FOTerm.app

def FOTerm.subst' := eval TermFnInterp

-- the same!
#eval arith_ex1.subst assign!{ x ↦ arith_ex2, y ↦ arith_ex3 }
#eval arith_ex1.subst' assign!{ x ↦ arith_ex2, y ↦ arith_ex3  }

/-
First-order semantics.

To handle the quantifiers, we only allow them to range over a fixed list
of elements.
-/

/-- an interpretation of relation symbols -/
def RelInterp α := FOAssignment (List α → Bool)

structure FOModel (α : Type) where
  (univ : List α)
  (fn : FnInterp α)
  (rel : RelInterp α)

-- coerces an association list to a function
instance [Inhabited α] : Coe (Std.AssocList String (List α → Bool)) (RelInterp α) :=
⟨fun l => l.getA⟩

def FOAssignment.update (σ : FOAssignment α) (x : String) (v : α) : FOAssignment α
  | y => if y == x then v else σ y

def FOForm.eval {α} [Inhabited α] [BEq α]
    (M : FOModel α) (σ : FOAssignment α) : FOForm → Bool
  | eq t1 t2 => t1.eval M.fn σ == t2.eval M.fn σ
  | rel r ts =>  M.rel r (ts.map $ FOTerm.eval M.fn σ)
  | tr => true
  | fls => false
  | neg A => !(eval M σ A)
  | conj A B => (eval M σ A) && (eval M σ B)
  | disj A B => (eval M σ A) || (eval M σ B)
  | impl A B => !(eval M σ A) || (eval M σ B)
  | biImpl A B => (!(eval M σ A) || (eval M σ B)) && (!(eval M σ B) || (eval M σ A))
  | ex x A => M.univ.any fun val => eval M (σ.update x val) A
  | all x A => M.univ.all fun val => eval M (σ.update x val) A

def babyArithMdl : FOModel Nat where
  univ := List.range 10  /- 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 -/
  fn   := arithFnInterp
  rel  := assign!{
            lt ↦ fun l : List Nat => if l.getA 0 < l.getA 1 then true else false,
            even ↦ fun l : List Nat => l.getA 0 % 2 == 0 }

def trivAssignment : FOAssignment Nat := fun _ => 0

-- don't forget the % in front of variables!

#eval fo!{even(%x)}.eval babyArithMdl assign!{x ↦ 5}
#eval fo!{even(%x)}.eval babyArithMdl assign!{x ↦ 6}
#eval fo!{∃ y. lt(%x, %y)}.eval babyArithMdl assign!{x ↦ 8}
#eval fo!{∃ y. lt(%x, %y)}.eval babyArithMdl assign!{x ↦ 9}

def FOForm.testeval (A : FOForm) : Bool := A.eval babyArithMdl trivAssignment

#eval fo!{even(two)}.testeval
#eval fo!{even(three)}.testeval
#eval fo!{∃ x. even(%x)}.testeval
#eval fo!{∀ x. even(%x)}.testeval

#eval fo!{∃ x. lt(%x, two) ∧ even(%x)}.testeval
#eval fo!{∃ x. ∃ y. lt(%x, %y) ∧ lt(%y, two) ∧ even(%x) ∧ even(%y)}.testeval
#eval fo!{∀ x. even(%x) ∧ lt(%x,two) → %x = zero}.testeval
#eval fo!{∀ x. even(%x) ∧ lt(%x,three) → %x = zero}.testeval
#eval fo!{∀ x. even(%x) ∧ lt(%x,three) → %x = zero ∨ %x = two}.testeval

#eval fo!{∀ x. ∃ y. lt(%x, %y)}.testeval
#eval fo!{∀ x. even(%x) → ∃ y. lt(%x, %y)}.testeval
#eval fo!{∀ x. ¬ even(%x) → ∃ y. lt(%x, %y)}.testeval

/-
Tarski's world
-/

inductive Shape where
  | tet
  | cube
  | dodec
deriving Repr, Inhabited, DecidableEq

inductive Size where
  | small
  | medium
  | large
deriving Repr, Inhabited, DecidableEq

def Size.lt : Size → Size → Bool
  | small, medium => true
  | small, large  => true
  | medium, large => true
  | _, _          => false

/-
Objects are placed on an 8 x 8 grid, but we won't check the range.
-/

structure Object :=
  (shape : Shape)
  (size : Size)
  (row : Nat)
  (col : Nat)
deriving Repr, Inhabited, DecidableEq

/-
Predicates
-/

open Shape Size

namespace Object

def isTet : Object → Bool
  | ⟨tet, _, _, _⟩ => true
  | _              => false

def isCube : Object → Bool
  | ⟨cube, _, _, _⟩ => true
  | _               => false

def isDodec : Object → Bool
  | ⟨dodec, _, _, _⟩ => true
  | _                => false

def isSmall : Object → Bool
  | ⟨_, small, _, _⟩ => true
  | _                => false

def isMedium : Object → Bool
  | ⟨_, medium, _, _⟩ => true
  | _                 => false

def isLarge : Object → Bool
  | ⟨_, large, _, _⟩ => true
  | _                 => false

def sameShape (x y : Object) : Bool := x.shape == y.shape

def sameSize (x y : Object) : Bool := x.size == y.size

def sameRow (x y : Object) : Bool := x.row == y.row

def sameCol (x y : Object) : Bool := x.col == y.col

def leftOf (x y : Object) : Bool := x.col < y.col

def rightOf (x y : Object) : Bool := y.col < x.col

def frontOf (x y : Object) : Bool := x.row < y.row

def backOf (x y : Object) : Bool := y.row < x.row

def smaller (x y : Object) : Bool := x.size.lt y.size

def larger (x y : Object) : Bool := y.size.lt x.size

def adjoins (x y : Object) : Bool :=
  (x.row = y.row - 1 || x.row = y.row || x.row = y.row + 1) &&
  (x.col = y.col - 1 || x.col = y.col || x.col = y.col + 1)

-- x is between y and z
def between (x y z : Object) : Bool :=
  -- same row
  (x.row == y.row && y.row == z.row &&
    ((y.col < x.col && x.col < z.col) || (z.col < x.col && x.col < y.col))) ||
  -- same column
  (x.col == y.col && y.col == z.col &&
    ((y.row < x.row && x.row < z.row) || (z.row < x.row && x.row < y.row))) ||
  -- same diagonal
  ( ((x.row + y.col == y.row + x.col && z.row + y.col == y.row + z.col) ||
      (x.row + x.col == y.row + y.col && z.row + z.col == y.row + y.col)) &&
    ((y.col < x.col && x.col < z.col) || (z.col < x.col && x.col < y.col)) &&
    ((y.row < x.row && x.row < z.row) || (z.row < x.row && x.row < y.row)))

end Object

def World := List Object

instance : ForIn m World Object := inferInstanceAs (ForIn m (List Object) Object)

/-
To print it out.
-/

instance : ToString Shape :=
  ⟨fun
    | tet =>   "T"
    | cube =>  "C"
    | dodec => "D"⟩

instance : ToString Size :=
  ⟨fun
    | small  => "-"
    | medium => " "
    | large  => "+"⟩

instance : ToString Object := ⟨fun obj : Object => (toString obj.shape) ++ (toString obj.size)⟩

instance : ToString (Option Object) :=
  ⟨fun
    | some obj => toString obj
    | none     => "  "⟩

def World.toArray (world : World) : Array (Array (Option Object)) := Id.run do
  let mut arr : Array (Array (Option Object)) := mkArray 8 (mkArray 8 none)
  for obj in world do
    assert! obj.row < 8
    assert! obj.col < 8
    arr := arr.set! obj.row $ arr[obj.row]!.set! obj.col (some obj)
  arr

instance : ToString World :=
  ⟨fun world => Id.run do
    let arr := world.toArray
    let rowDashes : String := "".pushn '-' 41
    let mut s := rowDashes ++ "\n"
    for i in [:8] do
      s := s ++ "| "
      for j in [:8] do
        s := s ++ toString (arr[7-i]!)[j]! ++ " | "
      s := s ++ "\n" ++ rowDashes ++ "\n"
    s⟩

def World.show (world : World) : IO Unit := do IO.print $ toString world

/-
Implement the language
-/

open Object in
def tWRelInterp : RelInterp Object :=
assign!{
  Tet       ↦ fun l : List Object => isTet (l.getA 0),
  Cube      ↦ fun l : List Object => isCube (l.getA 0),
  Dodec     ↦ fun l : List Object => isDodec (l.getA 0),
  Small     ↦ fun l : List Object => isSmall (l.getA 0),
  Medium    ↦ fun l : List Object => isMedium (l.getA 0),
  Large     ↦ fun l : List Object => isLarge (l.getA 0),
  SameShape ↦ fun l : List Object => sameShape (l.getA 0) (l.getA 1),
  SameSize  ↦ fun l : List Object => sameSize (l.getA 0) (l.getA 1),
  SameRow   ↦ fun l : List Object => sameRow (l.getA 0) (l.getA 1),
  SameCol   ↦ fun l : List Object => sameCol (l.getA 0) (l.getA 1),
  LeftOf    ↦ fun l : List Object => leftOf (l.getA 0) (l.getA 1),
  RightOf   ↦ fun l : List Object => rightOf (l.getA 0) (l.getA 1),
  FrontOf   ↦ fun l : List Object => frontOf (l.getA 0) (l.getA 1),
  BackOf    ↦ fun l : List Object => backOf (l.getA 0) (l.getA 1),
  Smaller   ↦ fun l : List Object => smaller (l.getA 0) (l.getA 1),
  Larger    ↦ fun l : List Object => larger (l.getA 0) (l.getA 1),
  Adjoins   ↦ fun l : List Object => adjoins (l.getA 0) (l.getA 1),
  Between   ↦ fun l : List Object => between (l.getA 0) (l.getA 1) (l.getA 2)
}

def World.eval (world : World) (A : FOForm) : Bool :=
  A.eval { univ := world, fn := fun _ _ => default, rel := tWRelInterp } (fun _ => default)

/-
Try it out.
-/

-- textbook: myWorld
def myWorld : World := [
  ⟨tet, medium, 0, 2⟩,
  ⟨tet, small, 0, 4⟩,
  ⟨cube, small, 4, 4⟩,
  ⟨cube, medium, 5, 6⟩,
  ⟨dodec, small, 7, 0⟩,
  ⟨dodec, large, 7, 4⟩ ]

#eval myWorld.show

/-
-----------------------------------------
| D- |    |    |    | D+ |    |    |    |
-----------------------------------------
|    |    |    |    |    |    |    |    |
-----------------------------------------
|    |    |    |    |    |    | C  |    |
-----------------------------------------
|    |    |    |    | C- |    |    |    |
-----------------------------------------
|    |    |    |    |    |    |    |    |
-----------------------------------------
|    |    |    |    |    |    |    |    |
-----------------------------------------
|    |    |    |    |    |    |    |    |
-----------------------------------------
|    |    | T  |    | T- |    |    |    |
-----------------------------------------
-/
-- end

-- Don't forget to put % before variables!

#eval myWorld.eval fo!{∃ x. ∃ y. ∃ z. Between(%x, %y, %z)}
#eval myWorld.eval fo!{∃ x. ∃ y. ∃ z. Cube(%x) ∧ Between(%x, %y, %z)}
#eval myWorld.eval fo!{∃ x. ∃ y. ∃ z. Dodec(%x) ∧ Between(%x, %y, %z)}
#eval myWorld.eval fo!{∃ x. Small(%x)}
#eval myWorld.eval fo!{∃ x. Small(%x) ∧ Cube(%x) }
#eval myWorld.eval fo!{∀ x. ∀ y. Cube(%x) ∧ Tet(%y) → FrontOf(%x, %y)}
#eval myWorld.eval fo!{∀ x. ∀ y. Cube(%x) ∧ Dodec(%y) → FrontOf(%x, %y)}
#eval myWorld.eval fo!{∀ x. Tet(%x) → ∃ y. Cube(%y) ∧ RightOf(%y, %x) }
#eval myWorld.eval fo!{∀ x. Dodec(%x) → ∃ y. Tet(%y) ∧ RightOf(%y, %x) }
