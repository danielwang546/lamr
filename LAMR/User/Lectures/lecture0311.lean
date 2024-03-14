import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import LAMR

variable (P Q R S : Prop)

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

/-
Proof terms
-/

def prod_swap (α β : Type) : α × β → β × α :=
  fun p => Prod.mk (Prod.snd p) (Prod.fst p)
--  fun p => ⟨p.2, p.1⟩

theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P :=
  fun p => And.intro (And.right p) (And.left p)
--  fun p => ⟨p.2, p.1⟩

def sum_swap (α β : Type) : Sum α β → Sum β α :=
  fun p =>
  match p with
    | Sum.inl a => Sum.inr a
    | Sum.inr b => Sum.inl b

theorem or_swap (P Q : Prop) : P ∨ Q → Q ∨ P :=
  fun p =>
  match p with
    | Or.inl a => Or.inr a
    | Or.inr b => Or.inl b

#explode and_swap
#explode or_swap

variable (P Q R : Prop)

example : P → P ∧ P := fun h : P => And.intro h h

example : P → P ∧ P := fun h : P => ⟨h, h⟩

example (h1 : P → Q) (h2 : P) : Q := h1 h2

example : P → ¬ P → Q := fun (h : P) (h' : ¬ P) => False.elim (h' h)

example : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.2, h.1⟩

example : P → Q → (P ∧ Q) ∨ R := by
  intro h1 h2
  exact Or.inl ⟨h1, h2⟩

theorem and_swap' : P ∧ Q → Q ∧ P := by
  intro h
  rcases h with ⟨h1, h2⟩
  constructor
  . exact h2
  . exact h1

theorem or_swap' : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with h1 |  h2
  . right; exact h1
  . left; exact h2

#print and_swap'
#explode and_swap'
#print or_swap'
#explode or_swap'

-- show term
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  exact And.casesOn h fun h1 h2 => { left := h2, right := h1 }

/-
Using `have`
-/

example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  apply h2
  apply h1
  exact h3

theorem foo (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  have h4 : Q := by
    apply h1
    exact h3
  apply h2
  exact h4

#print foo

example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  have h4 := h1 h3
  exact h2 h4

example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  exact h2 (h1 h3)

example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := h2 (h1 h3)

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

example (h : a = b) : b = a := by
  rw [h]

example (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

#check (mul_assoc : ∀ a b c, (a * b) * c = a * (b * c))
#check (mul_comm : ∀ a b, a * b = b * a)
#check (mul_left_comm : ∀ a b c, a * (b * c) = b * (a * c))

example : (c * b) * a = b * (a * c) := by
  rw [mul_comm c, mul_assoc, mul_comm c]

example : (a * b) * c = b * (a * c) := by
  sorry

example (a b c d e : ℕ) (h1 : a = b + 1)
    (h2 : d = c + a) (h3 : e = b + c) :
  d = e + 1 := by
  sorry

example (a b c d e : ℕ) (h1 : a = b + 1) (h2 : d = c + a) (h3 : e = b + c) : d = e + 1 := by
  sorry

example (h : a = a * a) : b * a = b * (a * a) := by
  sorry

example : 123 * 345 = 42435 := by
  norm_num

example : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring

example : a^2 - b^2 = (a + b) * (a - b) := by
  ring

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib (n + 1) + fib n

#eval fib 12

example : fib (n + 3) = 2 * fib (n + 1) + fib n := by
  rw [fib, fib]
  ring

section
variable (P Q : Prop)

#check (not_and_or : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q)
#check (not_not : ¬ ¬ P ↔ P)

example : ¬ (P ∧ ¬ Q) ↔ ¬ P ∨ Q := by
  rw [not_and_or, not_not]

end

example (n : Nat) : n + 0 = n := by
  rfl

example : fib 8 = 21 := by
  simp [fib]

example : a + b - b = a := by
  simp only [add_sub_cancel]

example : P ↔ P ∧ P := by
  simp

/-
Induction
-/

def sum_up_to : Nat → Nat
  | 0 => 0
  | (n + 1) => (n + 1) + sum_up_to n

example (n : Nat) : 2 * sum_up_to n = n * (n + 1) := by
  induction n with
  | zero => rw [sum_up_to]
  | succ n ih =>
      rw [sum_up_to, mul_add, ih, Nat.succ_eq_add_one]
      ring
