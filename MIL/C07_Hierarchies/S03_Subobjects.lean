import MIL.Common
import Mathlib.GroupTheory.QuotientGroup

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z ⟨a, haN, v, hvN, hxa⟩ ⟨b, hbN, w, hwN, hyb⟩
      use a * b, N.mul_mem haN hbN, v * w, N.mul_mem hvN hwN; calc
      x * (a * b) = x * a * b := by rw [← mul_assoc]
      _ = y * v * b := by rw [hxa]
      _ = y * (v * b) := by rw [mul_assoc]
      _ = y * (b * v) := by rw [mul_comm b v]
      _ = y * b * v := by rw [← mul_assoc]
      _ = z * w * v := by rw [hyb]
      _ = z * (w * v) := by rw [mul_assoc]
      _ = z * (v * w) := by rw [mul_comm w v]
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      intro a b ⟨w₁, hw₁, z₁, hz₁, h₁⟩ c d ⟨w₂, hw₂, z₂, hz₂, h₂⟩
      use w₁ * w₂, N.mul_mem hw₁ hw₂, z₁ * z₂, N.mul_mem hz₁ hz₂
      dsimp; calc
      a * c * (w₁ * w₂) = a * (c * (w₁ * w₂)) := by rw [← mul_assoc a]
      _ = a * (w₁ * w₂ * c) := by rw [mul_comm c]
      _ = a * (w₁ * (w₂ * c)) := by rw [mul_assoc w₁]
      _ = a * w₁ * (w₂ * c) := by rw [← mul_assoc a]
      _ = b * z₁ * (w₂ * c) := by rw [h₁]
      _ = b * z₁ * (c * w₂) := by rw [mul_comm w₂]
      _ = b * z₁ * (d * z₂) := by rw [h₂]
      _ = b * (z₁ * (d * z₂)) := by rw [mul_assoc b]
      _ = b * (d * z₂ * z₁) := by rw [mul_comm z₁]
      _ = b * (d * (z₂ * z₁)) := by rw [mul_assoc d]
      _ = b * d * (z₂ * z₁) := by rw [← mul_assoc b]
      _ = b * d * (z₁ * z₂) := by rw [mul_comm z₁]
      )
  mul_assoc := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
      apply Quotient.sound
      dsimp only
      rw [mul_assoc]
      apply @Setoid.refl M N.Setoid
  one := QuotientMonoid.mk N 1
  one_mul := by
      rintro ⟨a⟩
      apply Quotient.sound
      dsimp only
      rw [one_mul]
      apply @Setoid.refl M N.Setoid
  mul_one := by
      rintro ⟨a⟩
      apply Quotient.sound
      dsimp only
      rw [mul_one]
      apply @Setoid.refl M N.Setoid
