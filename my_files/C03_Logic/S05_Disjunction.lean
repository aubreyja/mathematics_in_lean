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

#print le_or_gt
#print abs_of_nonneg

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
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

#print le_neg
#print neg_pos

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]


theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw[abs_of_nonneg h]
    linarith[le_abs_self x, le_abs_self y]
  · rw[abs_of_neg h]
    linarith[neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  rcases le_or_gt 0 y with h | h
  · intro h₁
    left
    linarith [abs_of_nonneg h]
  · intro h₁
    right
    linarith [abs_of_neg h]
  · intro h₂
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
      rcases h₂ with hxy | hxny
      · exact hxy
      · linarith
    · rw [abs_of_neg h]
      rcases h₂ with hxy | hxny
      · linarith
      · exact hxny

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    intro h₁
    constructor
    linarith
    assumption
  · rw [abs_of_neg h]
    intro h₁
    constructor
    linarith
    linarith
  rintro ⟨h₁,h₂⟩
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    assumption
  · rw [abs_of_neg h]
    linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨a,b,h₁ | h₂⟩; linarith[pow_two_nonneg a,pow_two_nonneg b]; linarith[pow_two_nonneg a,pow_two_nonneg b]

#check eq_zero_or_eq_zero_of_mul_eq_zero

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have g: (x-1) * (x+1) =0 := by
    calc
    (x-1) * (x+1) = x^2 - 1 := by ring
    _= 1 - 1 := by rw[h]
    _= 0 := by norm_num
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g with h₁ | h₂
  left
  linarith[h₁]
  right
  linarith[h₂]

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have g : (x-y)*(x+y) = 0 := by
    calc
    (x-y)*(x+y) = x^2 - y^2 := by ring
    _= x^2 - x^2 := by rw[h]
    _= 0 := by apply sub_self
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g with h₁ | h₂
  left
  linarith[h₁]
  right
  linarith[h₂]

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have g: (x-1) * (x+1) =0 := by
    calc
    (x-1) * (x+1) = x^2 - 1 := by ring
    _= 1 - 1 := by rw[h]
    _= 0 := by norm_num
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g with h₁ | h₂
  left
  have : x = 1 := by
    calc
    x = x + 0 := by rw[add_zero]
    _= x + (1 - 1) := by rw[sub_self]
    _= x + (1 + -1) := by rw[sub_eq_add_neg]
    _= x + (-1 + 1) := by nth_rw 2 [add_comm]
    _= (x + -1) + 1 := by rw[← add_assoc]
    _= (x - 1) + 1 := by rw[← sub_eq_add_neg]
    _= 0 + 1 := by rw[h₁]
    _= 1 := by rw[zero_add]
  assumption
  right
  have : x = -1 := by
    calc
    x = x + 0 := by rw[add_zero]
    _= x + (1 - 1) := by rw[sub_self]
    _= x + (1 + -1) := by rw[sub_eq_add_neg]
    _= (x + 1) + -1 := by rw[← add_assoc]
    _= 0 + -1 := by rw[h₂]
    _= - 1 := by rw[zero_add]
  assumption

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have g : (x-y)*(x+y) = 0 := by
    calc
    (x-y)*(x+y) = x^2 - y^2 := by ring
    _= x^2 - x^2 := by rw[h]
    _= 0 := by apply sub_self
  rcases eq_zero_or_eq_zero_of_mul_eq_zero g with h₁ | h₂
  left
  have : x = y := by
    calc
    x = x + 0 := by rw[add_zero]
    _= x + (y - y) := by rw[sub_self]
    _= x + (y + -y) := by rw[sub_eq_add_neg]
    _= x + (-y + y) := by nth_rw 2 [add_comm]
    _= (x + -y) + y := by rw[← add_assoc]
    _= (x - y) + y := by rw[← sub_eq_add_neg]
    _= 0 + y := by rw[h₁]
    _= y := by rw[zero_add]
  assumption
  right
  have : x = -y := by
    calc
    x = x + 0 := by rw[add_zero]
    _= x + (y - y) := by rw[sub_self]
    _= x + (y + -y) := by rw[sub_eq_add_neg]
    _= (x + y) + -y := by rw[← add_assoc]
    _= 0 + -y := by rw[h₂]
    _= - y := by rw[zero_add]
  assumption

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  by_cases h' : P
  right
  apply h h'
  left
  assumption
  cases em P
  intro h₁
  rcases h₁ with np | q
  contradiction
  intro h₂
  assumption
  intro h₃
  intro h₄
  rcases h₃ with np | q
  contradiction
  assumption
