import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

--x ∈ f⁻¹'p means f x ∈ p (can use rfl). y ∈ f'' s decomposes to ⟨ x, xs, xeq ⟩ with
-- x : α satisfying xs : x ∈ s and xeq : f x = y (can use rfl in rintro to rw xeq)

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro h x xs
  have h₁ : f x ∈ f '' s := by exact mem_image_of_mem f xs
  have h₂ : f x ∈ v := by exact h h₁
  exact h₂
--or exact h (mem_image_of_mem f xs)
  intro h y ymem
  rcases ymem with ⟨x, xs, fxeq⟩
  rw[← fxeq]
  apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x h₁
  rcases h₁ with ⟨y,ys,hy⟩
  have  h₂: y = x := by apply h hy
  rw[h₂] at ys
  exact ys

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x h₁
  rcases h₁ with ⟨y,ys,hy⟩
  rw[h hy] at ys
  exact ys

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x h₁
  rcases h₁ with ⟨y,ys,hy⟩
  simpa [h hy] using ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro y hy
  rcases hy with ⟨x,xfu,rfl⟩
  exact xfu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hy
  rcases h y with ⟨x,rfl⟩
  simp
  use x

  example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hy
  rcases h y with ⟨x, rfl⟩
  use x
  constructor
  · exact hy
  · rfl

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y hy
  rcases hy with ⟨x,xs,fxeqy⟩
  use x
  constructor
  · exact h xs
  · exact fxeqy

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x hx
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  intro h₁
  rcases h₁ with (xfu|xfv)
  left
  exact xfu
  right
  exact xfv
  intro h₂
  rcases h₂ with (xfu|xfv)
  left
  exact xfu
  right
  exact xfv

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y h
  rcases h with ⟨x,xst,rfl⟩
  rcases xst with ⟨xs,xt⟩
  constructor
  use x
  use x

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  · exact ⟨x, xs, rfl⟩
  · exact ⟨x, xt, rfl⟩

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y h
  rcases h with ⟨x, hx, rfl⟩
  rcases hx with ⟨xs, xt⟩
  constructor
  · exact ⟨x, xs, rfl⟩
  · exact ⟨x, xt, rfl⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y ⟨⟨x₁,x₁s,fx₁y⟩,⟨x₂,x₂t,fx₂y⟩⟩
  have h₁ : f x₁ = f x₂ := by
   calc
   f x₁ = y := by exact fx₁y
   _ = f x₂ := by exact fx₂y.symm
  have h₂ : x₁ = x₂ := by apply h h₁
  use x₁
  constructor
  constructor
  exact x₁s
  simpa[h₂]
  exact fx₁y

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, x₁s, fx₁y⟩, ⟨x₂, x₂t, fx₂y⟩⟩
  have h₁ : f x₁ = f x₂ := by
    calc
      f x₁ = y := fx₁y
      _ = f x₂ := fx₂y.symm
  have h₂ : x₁ = x₂ := h h₁
  exact ⟨x₁, ⟨x₁s, by simpa [h₂] using x₂t⟩, fx₁y⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x,xs,fxy⟩,ynft⟩
  have xnt : x ∉ t := by
    intro xt
    simp[fxy] at ynft
    apply ynft x
    exact xt
    exact fxy
  have h₁ : x ∈ s\t := by
    exact ⟨xs,xnt⟩
  simp
  use x

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, hy⟩
  refine ⟨x, ⟨xs, ?_⟩, rfl⟩
  intro xt
  apply hy
  exact ⟨x, xt, rfl⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨pfu,npfv⟩
  exact ⟨pfu,npfv⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  rintro ⟨⟨x,xs,rfl⟩, hyv⟩
  exact ⟨x,⟨xs,hyv⟩,rfl⟩
  rintro ⟨x,⟨xs,hyv⟩,rfl⟩
  exact ⟨⟨x,xs,rfl⟩, hyv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x,⟨xs,fxu⟩,rfl⟩
  exact ⟨⟨x,xs,rfl⟩ ,fxu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨hxs,hfxu⟩
  exact ⟨⟨x,hxs,rfl⟩,hfxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs|fxu)
  exact Or.inl ⟨x,xs,rfl⟩; exact Or.inr fxu

  example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · simp
    exact Or.inl ⟨x, xs, rfl⟩
  · simp
    exact Or.inr fxu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · simp [xs, mem_image_of_mem f]
  · simp [fxu]

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; constructor
  rintro ⟨x, ⟨j,xAj⟩, rfl⟩
  rw[mem_iUnion]
  --exact ⟨j,⟨x,xAj,rfl⟩⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y ⟨x,xiInt,hx⟩
  rw [mem_iInter] at xiInt
  simp
  intro i

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
