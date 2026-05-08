import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Tactic.Ring.RingNF

--PR this to mathlib
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

lemma max_eq_add_add_abs_sub (a b : α) : max a b = 2⁻¹  * (a + b + |a - b|) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

lemma min_eq_add_sub_abs_sub (a b : α) : min a b = 2⁻¹ * (a + b - |a - b|) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring
