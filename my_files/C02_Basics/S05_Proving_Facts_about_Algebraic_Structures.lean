import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
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
#check inf_le_of_left_le

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · show x ⊓ y ≤ y ⊓ x
    apply le_inf
    apply inf_le_right
    apply inf_le_left
  · show y ⊓ x ≤ x ⊓ y
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show x ⊓ y ⊓ z ≤  x ⊓ (y ⊓ z)
    apply le_inf
    · show x ⊓ y ⊓ z ≤  x
      apply le_trans
      apply inf_le_left
      apply inf_le_left
    · show x ⊓ y ⊓ z ≤ y ⊓ z
      apply le_inf
      · show x ⊓ y ⊓ z ≤ y
        have h₁ : x ⊓ y ≤ y := by apply inf_le_right
        exact inf_le_of_left_le h₁
      · show x ⊓ y ⊓ z ≤ z
        exact inf_le_right
  · show x ⊓ (y ⊓ z) ≤  x ⊓ y ⊓ z
    apply le_inf
    · show x ⊓ (y ⊓ z) ≤ x ⊓ y
      apply le_inf
      · show x ⊓ (y ⊓ z) ≤ x
        apply inf_le_left
      · show x ⊓ (y ⊓ z) ≤ y
        have h₂ : y ⊓ z ≤ y := by apply inf_le_left
        exact inf_le_of_right_le h₂
    · show x ⊓ (y ⊓ z) ≤ z
      have h₃: y ⊓ z ≤ z := by apply inf_le_right
      have h₄: x ⊓ (y ⊓ z) ≤ y ⊓ z := by apply inf_le_right
      exact le_trans h₄ h₃

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · show x ⊔ y ≤ y ⊔ x
    have h₀ : x ≤ y ⊔ x := by apply le_sup_right
    have h₁ : y ≤ y ⊔ x := by apply le_sup_left
    exact sup_le h₀ h₁
  · show y ⊔ x ≤ x ⊔ y
    have h₂ : x ≤ x ⊔ y := by apply le_sup_left
    have h₃ : y ≤ x ⊔ y := by apply le_sup_right
    exact sup_le h₃ h₂

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    · show x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le
      · show x ≤ x ⊔ (y ⊔ z)
        apply le_sup_left
      · show y ≤ x ⊔ (y ⊔ z)
        have h₀ : y ≤ y ⊔ z := by apply le_sup_left
        have h₁ : y ⊔ z ≤ x ⊔ (y ⊔ z) := by apply le_sup_right
        exact le_trans h₀ h₁
    · show z ≤ x ⊔ (y ⊔ z)
      have h₂ : z ≤ y ⊔ z := by apply le_sup_right
      have h₃ : y ⊔ z ≤ x ⊔ (y ⊔ z) := by apply le_sup_right
      exact le_trans h₂ h₃
  · show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z
    apply sup_le
    · show x ≤ x ⊔ y ⊔ z
      have h₄ : x ≤ x ⊔ y := by apply le_sup_left
      have h₅ : x ⊔ y ≤ x ⊔ y ⊔ z := by apply le_sup_left
      exact le_trans h₄ h₅
    · show y ⊔ z ≤ x ⊔ y ⊔ z
      apply sup_le
      · show y ≤ x ⊔ y ⊔ z
        have h₆ : y ≤ x ⊔ y := by apply le_sup_right
        have h₇ : x ⊔ y ≤ x ⊔ y ⊔ z := by apply le_sup_left
        exact le_trans h₆ h₇
      · show z ≤ x ⊔ y ⊔ z
        exact le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · show x ⊓ (x ⊔ y) ≤ x
    exact inf_le_left
  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    · show x ≤ x
      apply le_refl
    · show x ≤ x ⊔ y
      apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · show x ⊔ x ⊓ y ≤ x
    have h₀ : x ≤ x := by apply le_refl
    have h₁ : x ⊓ y ≤ x := by apply inf_le_left
    apply sup_le h₀ h₁
  · show x ≤ x ⊔ x ⊓ y
    apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
#check sub_self

example (h : a ≤ b) : 0 ≤ b - a := by
  rw[← sub_self a]
  rw[sub_eq_add_neg,sub_eq_add_neg]
  apply add_le_add_right
  exact h

example (h: 0 ≤ b - a) : a ≤ b := by
  rw[← add_zero a]
  rw[← sub_add_cancel b a]
  rw[add_comm (b-a)]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₀ : 0 ≤ b - a := by
    rw[← sub_self a]
    rw[sub_eq_add_neg,sub_eq_add_neg]
    apply add_le_add_right
    exact h
  have h₁ : 0 ≤ (b-a) * c := by apply mul_nonneg h₀ h'
  rw [sub_mul] at h₁
  have h₂ : 0 + a * c ≤ b * c - a * c + a * c := by apply add_le_add_right h₁
  rw [zero_add] at h₂
  rw [sub_eq_add_neg] at h₂
  rw [add_assoc] at h₂
  rw [neg_add_cancel] at h₂
  rw [add_zero] at h₂
  exact h₂
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

#check nonneg_of_mul_nonneg_left

example (x y : X) : 0 ≤ dist x y := by
  have h : dist x x ≤ dist x y + dist y x := by apply dist_triangle
  rw[dist_self] at h
  rw[dist_comm] at h
  rw[← two_mul] at h
  rw[dist_comm] at h
  rw[mul_comm] at h
  exact nonneg_of_mul_nonneg_left h zero_lt_two
end
