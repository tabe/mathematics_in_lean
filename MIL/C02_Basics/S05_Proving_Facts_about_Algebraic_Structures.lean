import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    · apply inf_le_right
    · apply inf_le_left

theorem my_le_inf_left { a b c : α } : a ≤ b → c ⊓ a ≤ b := by
  intro h
  have h1 : c ⊓ a ≤ a := by apply inf_le_right
  apply le_trans h1 h

theorem my_le_inf_right { a b c : α } : a ≤ b → a ⊓ c ≤ b := by
  intro h
  rw [inf_comm]
  exact my_le_inf_left h

theorem my_le_inf_inf_left { a b c : α } : a ≤ b → c ⊓ a ≤ c ⊓ b := by
  intro h
  apply le_inf
  · apply inf_le_left
  · exact my_le_inf_left h

theorem my_le_inf_inf_right { a b c : α } : a ≤ b → a ⊓ c ≤ b ⊓ c := by
  intro h
  rw [inf_comm]
  apply le_inf
  · exact my_le_inf_left h
  · exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · exact my_le_inf_right inf_le_left
    · exact my_le_inf_inf_right inf_le_right
  · apply le_inf
    · exact my_le_inf_inf_left inf_le_left
    · exact my_le_inf_left inf_le_right

example : x ⊔ y = y ⊔ x := by
  exact sup_comm

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  exact sup_assoc

theorem my_inf_self { a : α } : a ⊓ a = a := by
  apply le_antisymm
  · exact inf_le_left
  · apply le_inf
    · exact le_rfl
    · exact le_rfl

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · exact inf_le_left
  · apply le_inf
    · exact le_rfl
    · exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · exact le_rfl
    · exact inf_le_left
  · exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

theorem my_le_sup_sup_left { x y z : α } : x ≤ y → z ⊔ x ≤ z ⊔ y := by
  intro h
  apply sup_le
  · exact le_sup_left
  · exact le_trans h le_sup_right

theorem my_le_sup_sup_right { x y z : α } : x ≤ y → x ⊔ z ≤ y ⊔ z := by
  intro h
  rw [sup_comm]
  apply sup_le
  · exact le_sup_right
  · exact le_trans h le_sup_left

theorem my_le_le_inf_inf { a b x y : α } ( h1 : a ≤ b ) ( h2 : x ≤ y ) : a ⊓ x ≤ b ⊓ y := by
  rw [inf_comm]
  apply le_inf
  · exact le_trans inf_le_right h1
  · exact le_trans inf_le_left h2

theorem my_le_le_sup_sup { a b x y : α } ( h1 : a ≤ b ) ( h2 : x ≤ y ) : a ⊔ x ≤ b ⊔ y := by
  rw [sup_comm]
  apply sup_le
  · exact le_trans h2 le_sup_right
  · exact le_trans h1 le_sup_left

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  have h1 : (a ⊔ b) ⊓ a = a := by
    apply le_antisymm
    · apply inf_le_right
    · exact le_inf le_sup_left le_rfl
  rw [h, h1]
  apply le_antisymm
  · apply my_le_sup_sup_left
    apply my_le_inf_inf_right
    exact le_sup_right
  · apply sup_le
    · exact le_sup_left
    · rw [inf_comm, h]
      apply my_le_le_sup_sup
      · exact inf_le_right
      · rw [inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  have h1 : (a ⊓ b) ⊔ a = a := by
    apply le_antisymm
    · exact sup_le inf_le_left le_rfl
    · exact le_sup_right
  rw [h, h1]
  apply le_antisymm
  · apply le_inf
    · exact inf_le_left
    · have h2 : a ⊓ b ⊔ c = c ⊔ a ⊓ b := by rw [sup_comm]
      rw [sup_comm, h2, h]
      apply my_le_le_inf_inf
      · exact le_sup_right
      · exact le_rfl
  · apply my_le_le_inf_inf
    · exact le_rfl
    · exact my_le_sup_sup_right inf_le_right
end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem my_le_zero_le_sub (h: a ≤ b) : 0 ≤ b - a := calc
  0 = -a + a := by simp
  _ ≤ -a + b := by apply add_le_add_left h
  _ = b - a := by apply neg_add_eq_sub

example (h : a ≤ b) : 0 ≤ b - a := by
  apply my_le_zero_le_sub
  exact h

theorem my_zero_le_sub_le (h: 0 ≤ b - a) : a ≤ b := calc
  a = a + 0 := by simp
  _ ≤ a + (b - a) := by apply add_le_add_left h
  _ = b := by simp

example (h: 0 ≤ b - a) : a ≤ b := by
  apply my_zero_le_sub_le
  exact h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ b - a := by
    apply my_le_zero_le_sub
    exact h
  have h2 : 0 ≤ (b - a) * c := by
    exact mul_nonneg h1 h'
  have h3 : (b - a) * c = b * c - a * c := by
    apply sub_mul
  have h4 : 0 ≤ b * c - a * c := by
    rw [h3] at h2
    exact h2
  apply my_zero_le_sub_le
  exact h4
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h1 : 0 ≤ dist x y * 2 := calc
    0 = dist x x := by rw [dist_self]
    _ ≤ dist x y + dist y x := by apply dist_triangle
    _ = dist x y + dist x y := by rw [dist_comm]
    _ = dist x y * 2 := by linarith
  have h2 : (0 : ℝ) < 2 := by simp
  apply nonneg_of_mul_nonneg_left h1 h2
end

