import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (P Q R S : Prop)

#check True
#check False
#check P ∧ Q
#check P ∨ Q
#check P → Q
#check P ↔ Q
#check ¬ P

theorem easy : P → P := by
  intro h
  apply h

#print easy

example : P → P := by
  intro h
  apply h

example : P → P := by
  intro h
  exact h

example (h1 : P → Q) (h2 : P) : Q := by
  apply h1
  exact h2

example : P → Q → P ∧ Q := by
  intro hP
  intro hQ
  constructor
  exact hP
  exact hQ

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  . exact hP
  . exact hQ

example : P ∧ Q → Q ∧ P := by
  intro hPQ
  rcases hPQ with ⟨hP, hQ⟩
  constructor
  . exact hQ
  . exact hP

example : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hP | hQ
  . right
    exact hP
  . left
    exact hQ

example (h : P → Q) : ¬ Q → ¬ P := by
  intro hnQ hP
  apply hnQ
  apply h
  exact hP

example (h : False) : P := by
  contradiction

example (h : False) : P := by
  rcases h

example (h1 : P) (h2 : ¬ P) : Q := by
  contradiction

example (h1 : P ∨ Q) (h2 : ¬ P) : Q := by
  -- by_contra h
  rcases h1 with hP | hQ
  . contradiction
  . assumption

/-
To prove `A ∧ B`, use `constructor`
To use `h : A ∧ B`, use `rcases ⟨hA, hB⟩`
To prove `A ∨ B`, use `left` or `right`
To use `h : A ∨ B`, use `rcases with hA | hB`
To prove `A → B`, use `intro h`
To use `h : A → B`, use `apply h`
To prove `¬ A`, use `intro h`
To use `h : ¬ A`, use `apply h`
To prove `False`, there is no canonical way
To use `h : False`, use `contradiction`
To prove `A ↔ B`, use `constructor`
To use `h : A ↔ B`, use `rcases ⟨hAB, hBA⟩`

When you need classical logic, use `by_cases h : A` or `by_contra h`,
-/

example (h1 : P ↔ Q) (h2 : P) : Q := by
  sorry

example (h1 : P ↔ Q) : Q ↔ P := by
  sorry

example (h1 : P → Q) : ¬ P ∨ Q := by
  by_cases h : P
  . right
    apply h1
    exact h
  . left
    exact h

/-
Equational reasoning
-/

section
variable (a b c d : Int)
variable (f : Int → Int)

example : f (a + b) = f (a + b) := by
  rfl

example (h : b = c) : f (a + b) = f (a + c) := by
  rw [h]

example (h1 : a = c) (h2 : b = d) : f (a + b) = f (c + d) := by
  rw [h1, h2]

example (h1 : a = c) (h2 : b = d) : f (a + b) = f (c + d) := by
  rw [←h1, h2]

example (h1 : a = c) (h2 : d = c + b) (h3 : d = e) :
    f (a + b) = f (e) := by
  rw [h1, ←h2, h3]
