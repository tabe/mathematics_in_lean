import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n h
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr; ring
    _ ≤ |s n - a| + |t n - b| := by apply abs_add
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      · apply hs _
        exact le_of_max_le_left h
      · apply ht _
        exact le_of_max_le_right h
    _ = ε := by norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  have cεpos : 0 < |ε / c| := by
    rw [abs_pos]
    apply div_ne_zero
    · linarith
    · exact h
  rcases cs |ε / c| cεpos with ⟨Ns, hs⟩
  use Ns
  intro n hn
  dsimp; calc
    |c * s n - c * a| = |c * (s n - a)| := by congr; ring
    _ = |c| * |s n - a| := by rw [abs_mul]
    _ < |c| * |ε / c| := mul_lt_mul_of_pos_left (hs n hn) acpos
    _ = |c * (ε / c)| := by rw [abs_mul]
    _ = |ε| := by
      congr
      apply mul_div_cancel'
      exact h
    _ = ε := abs_of_pos εpos
 
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hNn
  calc
    |s n| = |a + (s n - a)| := by congr; ring
    _ ≤ |a| + |s n - a| := by apply abs_add
    _ < |a| + 1 := by
      apply add_lt_add_left
      exact h n hNn

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n h
  have g₀ : n ≥ N₀ := by apply le_of_max_le_left h
  have g₁ : n ≥ N₁ := by apply le_of_max_le_right h
  calc
    |s n * t n - 0| = |s n * (t n - 0)| := by
       congr; ring
    _ = |s n| * |t n - 0| := by
      apply abs_mul
    _ < B * (ε / B) := by
      apply mul_lt_mul'' (h₀ n g₀) (h₁ n g₁)
      apply abs_nonneg
      apply abs_nonneg
    _ = ε := by
      apply mul_div_cancel'
      linarith

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    contrapose! abne
    have h : |a - b| = 0 := by
      apply le_antisymm abne
      apply abs_nonneg
    have : a - b = 0 := by
      rw [abs_eq_zero] at h
      exact h
    linarith
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have : N ≥ Na := by apply le_max_left
    exact hNa N this
  have absb : |s N - b| < ε := by
    have : N ≥ Nb := by apply le_max_right
    exact hNb N this
  have : |a - b| < |a - b| := calc
    |a - b| = |(s N - b) - (s N - a)| := by norm_num
    _ ≤ |s N - b| + |s N - a| := by apply abs_sub
    _ < ε + ε := by apply add_lt_add absb absa
    _ = |a - b| := by norm_num
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end

