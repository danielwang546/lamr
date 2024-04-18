import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
Implication and the universal quantifier
-/

section
variable (P Q R S : Nat → Prop)
variable (a b : Nat)

variable
  (h1 : ∀ x, P x → Q x)
  (h2 : ∀ x y, Q x → R y → S (x + y))
  (h3 : P a)
  (h4 : R b)

#check h1 a
#check h1 a h3
#check h2 a b (h1 a h3) h4

-- x and y are matched with a and b
example : S (a + b) := by
  apply h2
  . apply h1
    exact h3
  . exact h4

example : ∀ x y, P x → R y → S (x + y) := by
  intro u v hPu hRv
  apply h2
  . apply h1
    exact hPu
  . exact hRv

#check fun x y hP hR => h2 x y (h1 x hP) hR

end


section

variable (x y z w : ℤ)

#check add_lt_add_of_lt_of_le -- ∀ a b c d, a < b → c ≤ d → a + c < b + d
#check mul_le_mul_of_nonneg_left -- ∀ a b c, b ≤ c → 0 ≤ a → a * b ≤ a * c

example (h1 : x < y) (h2 : w ≤ z) : x + 3 * w < y + 3 * z := by
  apply add_lt_add_of_lt_of_le
  . apply h1
  . apply mul_le_mul_of_nonneg_left
    exact h2
    norm_num

#check mul_lt_mul'
#check le_of_lt
#check pow_two_nonneg

example (h1 : x < y) (h2 : z^2 < w^2) (h3 : 0 < y) :
    x * z^2 < y * w^2 := by
  apply mul_lt_mul'
  . apply le_of_lt
    exact h1
  . exact h2
  . apply pow_two_nonneg
  . exact h3

example (h1 : x < y) (h2 : z^2 < w^2) (h3 : 0 < y) :
    x * z^2 < y * w^2 :=
  mul_lt_mul' (le_of_lt h1) h2 (pow_two_nonneg _) h3

end

/-
So theorems can be applied to data and hypotheses
-/

theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
  x + z ≤ y + w := add_le_add h₁ h₂

section
variable (a b c d : ℝ)
variable (h₁ : a ≤ b)
variable (h₂ : c ≤ d)

#check my_add_le_add
#check my_add_le_add a b
#check my_add_le_add a b c d
#check my_add_le_add a b c d h₁
#check my_add_le_add a b c d h₁ h₂

end

/-
Implicit arguments -- just FYI. (We won't use them.)
-/

theorem my_add_le_add' {x y z w : ℝ} (h₁ : x ≤ y) (h₂ : z ≤ w) :
  x + z ≤ y + w := add_le_add h₁ h₂

section
variable (a b c d : ℝ)
variable (h₁ : a ≤ b)
variable (h₂ : c ≤ d)

#check my_add_le_add' h₁
#check my_add_le_add' h₁ h₂

end


/-
To prove ∀ x, P x : `intro x`, and then prove `P x`.

To use `h : ∀ x, P x`, apply it.
-/

section

variable {α β : Type} (p q r : α → Prop)

example (h1 : ∀ x, p x → q x) (h2 : ∀ x, p x) : ∀ x, q x := by
  intro x
  apply h1
  apply h2

example (h1 : ∀ x, p x → q x) (h2 : ∀ x, q x → r x) : ∀ x, p x → r x := by
  intro x hpx
  apply h2
  apply h1
  exact hpx

/-
The existential quantifier.

To prove `∃ x, p x`, use `use`.

To use `h : ∃ x, p x`, use `rcases h with ⟨x, px⟩`.
-/

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 2.5
  norm_num

example (h1 : ∃ x, p x) (h2 : ∀ x, p x → q x) : ∃ x, q x := by
  rcases h1 with ⟨x, px⟩
  use x
  apply h2
  exact px

example (h : ∃ x, p x) : ∃ x, p x ∨ q x := by
  rcases h with ⟨x, px⟩
  use x
  left
  exact px

end

/-
Injective and Surjective functions.
-/

open Function

#check Injective
#print Injective
#check Surjective
#print Surjective

variable (f : α → β) (g : β → γ)

example (Injf : Injective f) (Injg : Injective g) :
    Injective (g ∘ f) := by
  rw [comp, Injective]  -- can be omitted
  intro x1 x2
  intro heq
  have : f x1 = f x2 := by
    apply Injg heq
  apply Injf this

example (Surjf : Surjective f) (Surjg : Surjective g) :
    Surjective (g ∘ f) := by
  intro z
  have : ∃ y, g y = z := by
    apply Surjg
  rcases this with ⟨y, hy⟩
  rw [←hy, comp]; dsimp
  have : ∃ x, f x =y := by
    apply Surjf
  rcases this with ⟨x, hx⟩
  use x
  rw [hx]

example (Surjgf : Surjective (g ∘ f)) :
    Surjective g := by
  intro y
  have : ∃ x, g (f x) = y := by
    apply Surjgf
  rcases this with ⟨x, hx⟩
  use f x

example (Injgf : Injective (g ∘ f)) (Surjf : Surjective f) :
    Injective g := by
  intro y1 y2 h
  have h1 : ∃ x1, f x1 = y1 := by
    apply Surjf
  have h2 : ∃ x2, f x2 = y2 := by
    apply Surjf
  rcases h1 with ⟨x1, h1⟩
  rcases h2 with ⟨x2, h2⟩
  have : x1 = x2 := by
    apply Injgf
    rw [comp]; dsimp
    rw [h1, h2, h]
  rw [←h1, this, h2]


/-
Example from the textbook.
-/

section

variable {α : Type}
  (Student : α → Prop)
  (Owns : α → α → Prop)
  (Iphone : α → Prop)
  (Laptop : α → Prop)
  (Headphones : α → Prop)
  (Buggy : α → Prop)
  (Sad : α → Prop)
  (h1 : ∀ x, Student x → ∃ y, Owns x y ∧ (Iphone y ∨ Laptop y))
  (h2 : ∀ x y, Student x ∧ Owns x y ∧ Laptop y → ∃ z, Owns x z ∧ Headphones z)
  (h3 : ∀ y, Iphone y → Buggy y)
  (h4 : ∀ y, Headphones y → Buggy y)
  (h5 : ∀ x y, Student x ∧ Owns x y ∧ Buggy y → Sad x)

example : ∀ x, Student x → Sad x := by
  intro x hStx
  rcases h1 x hStx with ⟨y, hOwns, hI | hL⟩
  . apply h5 x y
    use hStx, hOwns
    apply h3
    apply hI
  . rcases h2 x y ⟨hStx, hOwns, hL⟩ with ⟨z, hOwns', hHead⟩
    apply h5 x z
    use hStx, hOwns'
    apply h4
    apply hHead

end
