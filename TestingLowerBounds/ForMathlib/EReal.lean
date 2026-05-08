import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open scoped ENNReal NNReal Topology
open Filter Set

namespace EReal

instance : CharZero EReal := inferInstanceAs (CharZero (WithBot (WithTop ℝ)))

instance : NoZeroDivisors EReal where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    contrapose! h
    induction a <;> induction b <;> try {· simp_all [← EReal.coe_mul]}

lemma lt_neg_iff_lt_neg {x y : EReal} : x < -y ↔ y < -x := by
  nth_rw 1 [← neg_neg x, neg_lt_neg_iff]

lemma le_neg_iff_le_neg {x y : EReal} : x ≤ -y ↔ y ≤ -x := by
  nth_rw 1 [← neg_neg x, neg_le_neg_iff]

lemma neg_le_iff_neg_le {x y : EReal} : -x ≤ y ↔ -y ≤ x := by
  nth_rw 1 [← neg_neg y, neg_le_neg_iff]

lemma top_mul_ennreal_coe {x : ℝ≥0∞} (hx : x ≠ 0) : ⊤ * (x : EReal) = ⊤ := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  · rw [← coe_ennreal_toReal hx_top, top_mul_coe_of_pos]
    exact ENNReal.toReal_pos hx hx_top

lemma ennreal_coe_mul_top {x : ℝ≥0∞} (hx : x ≠ 0) : (x : EReal) * ⊤ = ⊤ := by
  rw [mul_comm, top_mul_ennreal_coe hx]

lemma add_ne_top_iff_of_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  refine ⟨?_, fun h ↦ add_ne_top h.1 h.2⟩
  induction x <;> simp_all
  induction y <;> simp_all

lemma add_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y ≠ ⊥ :=
  add_ne_bot_iff.mpr ⟨hx, hy⟩

lemma coe_mul_add_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx_pos : 0 < x := hx_nonneg.lt_of_ne' hx0
  induction y
  · simp [EReal.coe_mul_bot_of_pos hx_pos]
  · induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · norm_cast
      rw [mul_add]
    · simp only [coe_add_top, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.coe_add_top]
  · simp only [EReal.coe_mul_top_of_pos hx_pos]
    induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · simp only [top_add_coe, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.top_add_coe]
    · simp [EReal.coe_mul_top_of_pos hx_pos]

lemma add_mul_coe_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    (y + z) * x = y * x + z * x := by
  simp_rw [mul_comm _ (x : EReal)]
  exact EReal.coe_mul_add_of_nonneg hx_nonneg y z

lemma add_sub_cancel (x : EReal) (y : ℝ) : x + y - y = x := by
  induction x
  · simp
  · norm_cast
    ring
  · simp

lemma add_sub_cancel' (x : EReal) (y : ℝ) : y + x - y = x := by
  rw [add_comm, EReal.add_sub_cancel]

lemma top_sub_of_ne_top {x : EReal} (hx : x ≠ ⊤) : ⊤ - x = ⊤ := by
  induction x <;> tauto

lemma top_mul_add_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⊤ * (x + y) = ⊤ * x + ⊤ * y := by
  induction x, y using EReal.induction₂_symm with
  | symm h =>
    rw [add_comm, add_comm (⊤ * _)]
    exact h hy hx
  | top_top => simp
  | top_pos _ h =>
    rw [top_add_coe, top_mul_top, top_mul_of_pos, top_add_top]
    exact mod_cast h
  | top_zero => simp
  | top_neg _ h =>
    refine absurd hy ?_
    exact mod_cast Std.not_le.mpr h
  | top_bot => simp
  | pos_bot => simp
  | coe_coe x y =>
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hx_pos : 0 < (x : EReal) := by
      refine hx.lt_of_ne' ?_
      exact mod_cast hx0
    have hy_pos : 0 < (y : EReal) := by
      refine hy.lt_of_ne' ?_
      exact mod_cast hy0
    rw [top_mul_of_pos hx_pos, top_mul_of_pos hy_pos, top_mul_of_pos]
    · simp
    · exact EReal.add_pos hx_pos hy_pos
  | zero_bot => simp
  | neg_bot => simp
  | bot_bot => simp

lemma mul_add_coe_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * (y + z) = x * y + x * z := by
  by_cases hx_top : x = ⊤
  · rw [hx_top]
    exact top_mul_add_of_nonneg (mod_cast hy) (mod_cast hz)
  by_cases hx_bot : x = ⊥
  · rw [hx_bot]
    by_cases hy0 : y = 0
    · simp [hy0]
    by_cases hz0 : z = 0
    · simp [hz0]
    have hy_pos : 0 < (y : EReal) := lt_of_le_of_ne' (mod_cast hy) (mod_cast hy0)
    have hz_pos : 0 < (z : EReal) := lt_of_le_of_ne' (mod_cast hz) (mod_cast hz0)
    rw [bot_mul_of_pos hy_pos, bot_mul_of_pos hz_pos, bot_mul_of_pos]
    · simp
    · exact EReal.add_pos hy_pos hz_pos
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  norm_cast
  rw [mul_add]

lemma coe_add_mul_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (y + z) * x =  y * x + z * x := by
  simp_rw [mul_comm _ x]
  exact EReal.mul_add_coe_of_nonneg x hy hz

instance : MeasurableAdd₂ EReal := ⟨EReal.lowerSemicontinuous_add.measurable⟩

section MeasurableMul

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

theorem measurable_from_prod_countable'' [Countable β] [MeasurableSingletonClass β]
    {f : β × α → γ} (hf : ∀ y, Measurable fun x => f (y, x)) :
    Measurable f := by
  change Measurable ((fun (p : α × β) ↦ f (p.2, p.1)) ∘ Prod.swap)
  exact (measurable_from_prod_countable_left hf).comp measurable_swap

theorem measurable_of_measurable_real_prod {f : EReal × β → γ}
    (h_real : Measurable fun p : ℝ × β ↦ f (p.1, p.2))
    (h_bot : Measurable fun x ↦ f (⊥, x)) (h_top : Measurable fun x ↦ f (⊤, x)) :
    Measurable f := by
  have : (univ : Set (EReal × β)) = ({⊥, ⊤} ×ˢ univ) ∪ ({⊥, ⊤}ᶜ ×ˢ univ) := by
    ext x
    simp only [mem_univ, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, and_true,
      mem_compl_iff, not_or, true_iff]
    tauto
  refine measurable_of_measurable_union_cover ({⊥, ⊤} ×ˢ univ)
    ({⊥, ⊤}ᶜ ×ˢ univ) ?_ ?_ ?_ ?_ ?_
  · refine MeasurableSet.prod ?_ MeasurableSet.univ
    simp only [measurableSet_insert, MeasurableSet.singleton]
  · refine (MeasurableSet.compl ?_).prod MeasurableSet.univ
    simp only [measurableSet_insert, MeasurableSet.singleton]
  · rw [this]
  · let e : ({⊥, ⊤} ×ˢ univ : Set (EReal × β)) ≃ᵐ ({⊥, ⊤} : Set EReal) × β :=
      (MeasurableEquiv.Set.prod ({⊥, ⊤} : Set EReal) (univ : Set β)).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.Set.univ β))
    have : ((fun (a : ({⊥, ⊤} : Set EReal) × β) ↦ f (a.1, a.2)) ∘ e)
        = fun (a : ({⊥, ⊤} ×ˢ univ : Set (EReal × β))) ↦ f a := rfl
    rw [← this]
    refine Measurable.comp ?_ e.measurable
    refine measurable_from_prod_countable'' fun y ↦ ?_
    simp only
    have h' := y.2
    simp only [mem_insert_iff, mem_singleton_iff] at h'
    cases h' with
    | inl h => rwa [h]
    | inr h => rwa [h]
  · let e : ({⊥, ⊤}ᶜ ×ˢ univ : Set (EReal × β)) ≃ᵐ ℝ × β :=
      (MeasurableEquiv.Set.prod ({⊥, ⊤}ᶜ : Set EReal) (univ : Set β)).trans
        (MeasurableEquiv.prodCongr MeasurableEquiv.erealEquivReal (MeasurableEquiv.Set.univ β))
    rw [← MeasurableEquiv.measurable_comp_iff e.symm]
    exact h_real

theorem measurable_of_measurable_real_real {f : EReal × EReal → β}
    (h_real : Measurable fun p : ℝ × ℝ ↦ f (p.1, p.2))
    (h_bot_left : Measurable fun r : ℝ ↦ f (⊥, r))
    (h_top_left : Measurable fun r : ℝ ↦ f (⊤, r))
    (h_bot_right : Measurable fun r : ℝ ↦ f (r, ⊥))
    (h_top_right : Measurable fun r : ℝ ↦ f (r, ⊤)) :
    Measurable f := by
  refine measurable_of_measurable_real_prod ?_ ?_ ?_
  · refine measurable_swap_iff.mp <| measurable_of_measurable_real_prod ?_ h_bot_right h_top_right
    exact h_real.comp measurable_swap
  · exact measurable_of_measurable_real h_bot_left
  · exact measurable_of_measurable_real h_top_left

private lemma measurable_const_mul (c : EReal) : Measurable fun (x : EReal) ↦ c * x := by
  refine measurable_of_measurable_real ?_
  sorry -- TODO
  -- induction c with
  -- | h_bot =>
  --   have : (fun (p : ℝ) ↦ (⊥ : EReal) * p)
  --       = fun p ↦ if p = 0 then (0 : EReal) else (if p < 0 then ⊤ else ⊥) := by
  --     ext p
  --     split_ifs with h1 h2
  --     · simp [h1]
  --     · rw [bot_mul_coe_of_neg h2]
  --     · rw [bot_mul_coe_of_pos]
  --       exact lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
  --   rw [this]
  --   refine Measurable.piecewise (measurableSet_singleton _) measurable_const ?_
  --   exact Measurable.piecewise measurableSet_Iio measurable_const measurable_const
  -- | h_real c => exact (measurable_id.const_mul _).coe_real_ereal
  -- | h_top =>
  --   have : (fun (p : ℝ) ↦ (⊤ : EReal) * p)
  --       = fun p ↦ if p = 0 then (0 : EReal) else (if p < 0 then ⊥ else ⊤) := by
  --     ext p
  --     split_ifs with h1 h2
  --     · simp [h1]
  --     · rw [top_mul_coe_of_neg h2]
  --     · rw [top_mul_coe_of_pos]
  --       exact lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
  --   rw [this]
  --   refine Measurable.piecewise (measurableSet_singleton _) measurable_const ?_
  --   exact Measurable.piecewise measurableSet_Iio measurable_const measurable_const

instance : MeasurableMul₂ EReal := by
  refine ⟨measurable_of_measurable_real_real ?_ ?_ ?_ ?_ ?_⟩
  · exact (measurable_fst.mul measurable_snd).coe_real_ereal
  · exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · simp_rw [mul_comm _ ⊥]
    exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · simp_rw [mul_comm _ ⊤]
    exact (measurable_const_mul _).comp measurable_coe_real_ereal

end MeasurableMul
end EReal

namespace ENNReal

variable {a b c x y : ℝ≥0∞}

--PR these 2 lemmas to mathlib, just after ENNReal.mul_max
-- #check ENNReal.mul_max
theorem min_mul : min a b * c = min (a * c) (b * c) := mul_left_mono.map_min

theorem mul_min : a * min b c = min (a * b) (a * c) := mul_right_mono.map_min

@[simp]
lemma toReal_toEReal_of_ne_top (hx : x ≠ ⊤) : x.toReal.toEReal = x.toEReal := by
  cases x <;> tauto

end ENNReal
