import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply max_comm
example : min (min a b) c = min a (min b c) := by
  apply min_assoc
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h1 : min a b ≤ a := by
    apply min_le_left
  have h2 : min a b ≤ b := by
    apply min_le_right
  have h3 : min a b + c ≤ a + c := by
    apply add_le_add_right h1
  have h4 : min a b + c ≤ b + c := by
    apply add_le_add_right h2
  rw [le_min_iff]
  exact And.intro h3 h4
theorem my_aux : min (a + c) (b + c) ≤ min a b + c := by
  have h1 : min a b = a ∨ min a b = b := by
    apply min_choice
  apply Or.elim h1
  · intro h2
    rw [h2]
    apply min_le_left
  · intro h3
    rw [h3]
    apply min_le_right
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  apply my_aux
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := calc
  |a| - |b| = |a - b + b| - |b| := by rw [sub_add, sub_self, sub_zero]
  _ ≤ |a - b| + |b| - |b| := sub_le_sub_right (abs_add (a - b) b) |b|
  _ = |a - b| := by rw [← add_sub, sub_self, add_zero]
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h0 : x ∣ y * (x * z) := by
    apply dvd_mul_of_dvd_right
    apply dvd_mul_of_dvd_left dvd_rfl
  have h1 : x ∣ x ^ 2 := by
    apply dvd_pow dvd_rfl
    linarith
  have h2 : x ∣ y * (x * z) + x ^ 2 := dvd_add h0 h1
  have h3 : x ∣ w ^ 2 := by
    apply dvd_pow h
    linarith
  apply dvd_add h2 h3
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := gcd_comm m n

end


