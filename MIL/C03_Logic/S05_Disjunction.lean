import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · linarith [abs_of_neg h]

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · linarith [abs_of_nonneg h]
  · linarith [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  . rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · intro h
    rcases le_or_gt 0 y with g | g
    · rw [abs_of_nonneg g] at h
      left
      exact h
    · rw [abs_of_neg g] at h
      right
      exact h
  · intro h
    rcases h with g | g
    · linarith [le_abs_self y]
    · linarith [neg_le_abs_self y]

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    rcases le_or_gt 0 x with g | g
    · rw [abs_of_nonneg g] at h
      constructor
      · linarith
      · exact h
    · rw [abs_of_neg g] at h
      constructor
      · linarith
      · linarith
  · intro h
    rcases le_or_gt 0 x with g | g
    · rw [abs_of_nonneg g]
      linarith
    · rw [abs_of_neg g]
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨a, ⟨b, rfl | rfl⟩⟩; linarith [pow_two_nonneg a, pow_two_nonneg b]; linarith [pow_two_nonneg a, pow_two_nonneg b]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have g : (x - 1) * (x + 1) = 0 := calc
    (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
    _ = 0 := by rw [h]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g with f | f
  · left; linarith
  · right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have g : (x - y) * (x + y) = 0 := calc
    (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
    _ = 0 := by rw [h]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g with f | f
  · left; linarith
  · right; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have g : (x - 1) * (x + 1) = 0 := calc
    (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
    _ = 0 := by rw [h]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g with f | f
  · left; calc
    x = x - 1 + 1 := by rw [sub_add]; ring
    _ = 1 := by rw [f]; ring
  · right; calc
    x = x + 1 + -1 := by rw [add_assoc]; ring
    _ = -1 := by rw [f]; ring

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have g : (x - y) * (x + y) = 0 := calc
    (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
    _ = 0 := by rw [h]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g with f | f
  · left; calc
    x = x - y + y := by rw [sub_add]; ring
    _ = y := by rw [f]; ring
  · right; calc
    x = x + y + -y := by rw [add_assoc]; ring
    _ = -y := by rw [f]; ring

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right; exact h h'
    · left; exact h'
  · intro h
    rcases h with h' | h'
    · intro h''; contradiction
    · intro _; exact h'
