/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import TestingLowerBounds.CurvatureMeasure
import TestingLowerBounds.Divergences.StatInfo.StatInfo
import TestingLowerBounds.FDiv.Measurable

/-!
# fDiv and StatInfo

-/

open MeasureTheory Set

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} {π : Measure Bool} {f : ℝ → ℝ} {β γ x t : ℝ}

section StatInfoFun

open Set Filter ConvexOn

lemma nnreal_mul_fDiv_statInfoFun {a : NNReal} :
    a * fDiv (statInfoFun β γ) μ ν = fDiv (fun x ↦ statInfoFun (a * β) (a * γ) x) μ ν := by
  change (a.1 : EReal) * _ = _
  rw [← fDiv_mul a.2 ((convexOn_statInfoFun β γ).subset (fun _ _ ↦ trivial) (convex_Ici 0)) μ ν]
  simp_rw [const_mul_statInfoFun a.2]
  rfl

lemma fDiv_statInfoFun_nonneg : 0 ≤ fDiv (statInfoFun β γ) μ ν :=
  fDiv_nonneg_of_nonneg (fun x ↦ statInfoFun_nonneg β γ x) (derivAtTop_statInfoFun_nonneg β γ)

lemma stronglyMeasurable_fDiv_statInfoFun (μ ν : Measure 𝒳) [SFinite ν] :
    StronglyMeasurable (Function.uncurry fun β γ ↦ fDiv (statInfoFun β γ) μ ν) := by
  simp_rw [fDiv]
  have h_meas := stronglyMeasurable_statInfoFun.measurable.comp
    (f := fun ((a, b), x) ↦ ((a, b), ((∂μ/∂ν) x).toReal)) (measurable_fst.prod_mk (by fun_prop))
    |>.stronglyMeasurable
  refine Measurable.ite ?_ measurable_const ?_ |>.stronglyMeasurable
  · rw [← Set.compl_setOf, MeasurableSet.compl_iff]
    exact measurableSet_integrable h_meas
  · refine StronglyMeasurable.integral_prod_right (by exact h_meas)
      |>.measurable.coe_real_ereal.add ?_
    simp_rw [derivAtTop_statInfoFun_eq]
    refine (Measurable.coe_real_ereal ?_).mul_const _
    apply Measurable.ite (measurableSet_le measurable_const measurable_fst)
      <;> refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) ?_ ?_ <;> fun_prop

lemma fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonneg_of_le hβ hγ, zero_mul, add_zero, statInfoFun_of_le hγ]

lemma fDiv_statInfoFun_eq_integral_max_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν
      = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν + β * (μ.singularPart ν) univ := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonneg_of_gt hβ hγ, statInfoFun_of_gt hγ]

lemma fDiv_statInfoFun_eq_integral_max_of_nonpos_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν
      = ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν - β * (μ.singularPart ν) univ := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonpos_of_le hβ hγ, statInfoFun_of_le hγ, neg_mul, ← sub_eq_add_neg]

lemma fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν := by
  simp_rw [fDiv_of_integrable (integrable_statInfoFun_rnDeriv _ _ _ _),
    derivAtTop_statInfoFun_of_nonpos_of_gt hβ hγ, statInfoFun_of_gt hγ, zero_mul, add_zero]

lemma fDiv_statInfoFun_eq_zero_of_nonneg_of_nonpos [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ 0) :
    fDiv (statInfoFun β γ) μ ν = 0 := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le hβ (hγ.trans hβ), EReal.coe_eq_zero]
  convert integral_zero 𝒳 ℝ with x
  exact max_eq_left <| tsub_nonpos.mpr <| hγ.trans <| mul_nonneg hβ ENNReal.toReal_nonneg

lemma fDiv_statInfoFun_eq_zero_of_nonpos_of_pos [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : 0 < γ) :
    fDiv (statInfoFun β γ) μ ν = 0 := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt hβ (hβ.trans_lt hγ), EReal.coe_eq_zero]
  convert integral_zero 𝒳 ℝ with x
  exact max_eq_left <| tsub_nonpos.mpr <|
    (mul_nonpos_iff.mpr <| Or.inr ⟨hβ, ENNReal.toReal_nonneg⟩).trans hγ.le

/-- Auxiliary lemma for `fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le` and
`fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_le`. -/
lemma integral_max_eq_integral_abs [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (γ - β * ((∂μ/∂ν) x).toReal) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν + γ * (ν univ).toReal - β * (μ univ).toReal
        + β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_eq_add_add_abs_sub, zero_add, zero_sub, neg_sub, integral_mul_left]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ γ - β * ((∂μ/∂ν) x).toReal) ν := (integrable_const γ).sub h_int
  rw [integral_add h_int', integral_sub (integrable_const γ) h_int, integral_const, smul_eq_mul,
    mul_comm, integral_mul_left, add_comm, add_sub_assoc, add_assoc, sub_eq_add_neg, sub_eq_add_neg,
    add_assoc, ← mul_neg, ← mul_neg, ← mul_add]
  swap; · exact (integrable_add_const_iff.mpr h_int).abs
  congr
  nth_rw 2 [μ.haveLebesgueDecomposition_add ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (μ.measurable_rnDeriv ν).aemeasurable (μ.rnDeriv_lt_top ν)]

/-- Auxiliary lemma for `fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt` and
`fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_gt`. -/
lemma integral_max_eq_integral_abs' [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫ x, max 0 (β * ((∂μ/∂ν) x).toReal - γ) ∂ν
      = 2⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν - γ * (ν univ).toReal + β * (μ univ).toReal
        - β * ((μ.singularPart ν) univ).toReal) := by
  simp_rw [max_eq_add_add_abs_sub, zero_add, zero_sub, abs_neg, integral_mul_left]
  congr
  have h_int : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv.const_mul _
  have h_int' : Integrable (fun x ↦ β * ((∂μ/∂ν) x).toReal - γ) ν := h_int.sub (integrable_const γ)
  rw [integral_add h_int', integral_sub h_int (integrable_const γ), integral_const, smul_eq_mul,
    mul_comm, integral_mul_left, add_comm, add_sub_assoc, sub_eq_add_neg, add_comm (β * _),
    ← add_assoc, ← sub_eq_add_neg]
  swap; · exact (h_int.sub (integrable_const _)).abs
  congr
  nth_rw 2 [μ.haveLebesgueDecomposition_add ν]
  simp only [Measure.coe_add, Pi.add_apply, MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ]
  rw [ENNReal.toReal_add (measure_ne_top _ _)]
  swap; · exact lt_top_iff_ne_top.mp <| (setLIntegral_univ _ ▸
    Measure.setLIntegral_rnDeriv_le univ).trans_lt IsFiniteMeasure.measure_univ_lt_top
  ring_nf
  rw [integral_toReal (μ.measurable_rnDeriv ν).aemeasurable (μ.rnDeriv_lt_top ν)]

lemma fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      + β * (μ.singularPart ν) univ + γ * ν univ - β * μ univ) := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_le hβ hγ, integral_max_eq_integral_abs,
    sub_eq_add_neg, add_assoc, add_comm (- _), ← add_assoc, ← sub_eq_add_neg, add_assoc,
    add_comm (_ * _), add_assoc]
  simp only [EReal.coe_mul, EReal.coe_sub, EReal.coe_add,
    EReal.coe_ennreal_toReal (measure_ne_top _ _)]

lemma fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      + β * (μ.singularPart ν) univ + β * μ univ - γ * ν univ) := by
  have h_eq :
      (β : EReal) * ((μ.singularPart ν) univ)
        = ↑(2⁻¹ * (2 * β * ((μ.singularPart ν) univ).toReal)) := by
    simp [mul_assoc, EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  rw [fDiv_statInfoFun_eq_integral_max_of_nonneg_of_gt hβ hγ, integral_max_eq_integral_abs', h_eq,
    ← EReal.coe_add, ← mul_add, EReal.coe_mul]
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, sub_eq_add_neg,
    ← EReal.coe_neg, ← EReal.coe_add, add_assoc]
  congr 3
  ring

lemma fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν) univ + γ * ν univ - β * μ univ) := by
  have h_eq :
      (β : EReal) * ((μ.singularPart ν) univ)
        = ↑(2⁻¹ * (2 * β * ((μ.singularPart ν) univ).toReal)) := by
    simp [mul_assoc, EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_le hβ hγ, integral_max_eq_integral_abs, h_eq,
    sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_add, ← mul_neg, ← mul_add, EReal.coe_mul]
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, sub_eq_add_neg,
    ← EReal.coe_neg, ← EReal.coe_add, add_assoc]
  congr 3
  ring

lemma fDiv_statInfoFun_eq_integral_abs_of_nonpos_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : β ≤ 0) (hγ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = (2 : ℝ)⁻¹ * (∫ x, |β * ((∂μ/∂ν) x).toReal - γ| ∂ν
      - β * (μ.singularPart ν) univ + β * μ univ - γ * ν univ) := by
  rw [fDiv_statInfoFun_eq_integral_max_of_nonpos_of_gt hβ hγ, integral_max_eq_integral_abs']
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, sub_eq_add_neg,
    ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_mul]
  ring_nf

lemma fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγβ : γ ≤ β) :
    fDiv (statInfoFun β γ) μ ν = statInfo μ ν (Bool.boolMeasure (.ofReal β) (.ofReal γ))
      + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + γ * (ν univ).toReal - β * (μ univ).toReal) := by
  rw [← ENNReal.toReal_toEReal_of_ne_top statInfo_ne_top, toReal_statInfo_eq_integral_abs]
  simp only [Bool.boolMeasure_apply_false, ENNReal.toReal_mul, hβ, ENNReal.toReal_ofReal,
    Bool.boolMeasure_apply_true, hγ, EReal.coe_mul, EReal.coe_add, EReal.coe_neg,
    ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)]
  rw [show 2⁻¹ = ((2⁻¹ : ℝ) : EReal) from rfl, ← EReal.coe_mul_add_of_nonneg (by positivity),
    fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_le hβ hγβ]
  simp_rw [sub_eq_add_neg, ← add_assoc]
  rw [add_comm (-_ + _ + _)]
  simp_rw [← add_assoc, ← sub_eq_add_neg, ]
  rw [EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _), zero_add]

lemma fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_gt [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hγβ : β < γ) :
    fDiv (statInfoFun β γ) μ ν = statInfo μ ν (Bool.boolMeasure (.ofReal β) (.ofReal γ))
      + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + β * (μ univ).toReal - γ * (ν univ).toReal) := by
  rw [← ENNReal.toReal_toEReal_of_ne_top statInfo_ne_top, toReal_statInfo_eq_integral_abs]
  simp only [Bool.boolMeasure_apply_false, ENNReal.toReal_mul, hβ, ENNReal.toReal_ofReal,
    Bool.boolMeasure_apply_true, hγ, EReal.coe_mul, EReal.coe_add, EReal.coe_neg,
    ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)]
  rw [show 2⁻¹ = ((2⁻¹ : ℝ) : EReal) from rfl, ← EReal.coe_mul_add_of_nonneg (by positivity),
    fDiv_statInfoFun_eq_integral_abs_of_nonneg_of_gt hβ hγβ]
  simp_rw [sub_eq_add_neg, ← add_assoc]
  rw [add_comm (-_ + _ + _)]
  simp_rw [← add_assoc, ← sub_eq_add_neg, ]
  rw [EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _), zero_add]

-- N.B. we cannot use the Real.sign function here because it is 0 at 0, but we need it to be -1.
lemma fDiv_statInfoFun_eq_StatInfo_of_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    fDiv (statInfoFun β γ) μ ν = statInfo μ ν (Bool.boolMeasure (.ofReal β) (.ofReal γ))
      + 2⁻¹ * (|β * (μ univ).toReal - γ * (ν univ).toReal|
        + (if γ ≤ β then -1 else 1) * (β * (μ univ).toReal - γ * (ν univ).toReal)) := by
  rcases le_or_lt γ β with (hβγ | hβγ)
  · rw [fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_le hβ hγ hβγ, if_pos hβγ, neg_one_mul,
      EReal.neg_sub, add_comm (-_), sub_eq_add_neg, add_assoc]
    · exact Or.inl <| EReal.add_top_iff_ne_bot.mp rfl
    · exact Or.inl <| Ne.symm (ne_of_beq_false rfl)
  · rw [fDiv_statInfoFun_eq_StatInfo_of_nonneg_of_gt hβ hγ hβγ, if_neg hβγ.not_le, one_mul,
      add_sub_assoc]

lemma fDiv_statInfoFun_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (statInfoFun β γ) μ ν ≠ ⊤ := by
  simp [derivAtTop_statInfoFun_ne_top, fDiv_ne_top_iff, integrable_statInfoFun_rnDeriv]

lemma integral_statInfoFun_curvatureMeasure (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    ∫ y, statInfoFun 1 y t ∂(curvatureMeasure f) = f t - f 1 - (rightDeriv f 1) * (t - 1) := by
  have : f t - f 1 - (rightDeriv f 1) * (t - 1) = ∫ x in (1)..t, t - x ∂(curvatureMeasure f) :=
    convex_taylor hf_cvx hf_cont
  rcases le_total t 1 with (ht | ht)
  · simp_rw [this, statInfoFun_of_one_of_right_le_one ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_ge ht, ← integral_neg, neg_sub]
  · simp_rw [this, statInfoFun_of_one_of_one_le_right ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le ht]

lemma integral_statInfoFun_curvatureMeasure' (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f)
    (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) :
    ∫ y, statInfoFun 1 y t ∂(curvatureMeasure f) = f t := by
  rw [integral_statInfoFun_curvatureMeasure hf_cvx hf_cont, hf_one, hfderiv_one, sub_zero, zero_mul,
    sub_zero]

lemma lintegral_f_rnDeriv_eq_lintegralfDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f)
    (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) (h_ac : μ ≪ ν) :
    ∫⁻ x, ENNReal.ofReal (f ((∂μ/∂ν) x).toReal) ∂ν
      = ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂curvatureMeasure f  := by
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry :=
    stronglyMeasurable_statInfoFun.measurable.comp <|
      (measurable_const.prod_mk measurable_snd).prod_mk <|
      ((μ.measurable_rnDeriv ν).comp measurable_fst).ennreal_toReal
  classical
  simp_rw [fDiv_of_absolutelyContinuous h_ac, if_pos (integrable_statInfoFun_rnDeriv 1 _ _ _),
    EReal.real_coe_toENNReal,
    ← integral_statInfoFun_curvatureMeasure' hf_cvx hf_cont hf_one hfderiv_one]
  have (x : 𝒳) : ENNReal.ofReal (∫ γ, statInfoFun 1 γ ((∂μ/∂ν) x).toReal ∂curvatureMeasure f) =
      ∫⁻ γ, ENNReal.ofReal (statInfoFun 1 γ ((∂μ/∂ν) x).toReal) ∂curvatureMeasure f := by
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun y ↦ statInfoFun_nonneg _ _ _)
        h_meas.of_uncurry_left.stronglyMeasurable.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal <| (lintegral_ofReal_le_lintegral_nnnorm _).trans_lt ?_ |>.ne
    exact (integrable_statInfoFun 1 _).hasFiniteIntegral
  simp_rw [this]
  rw [lintegral_lintegral_swap h_meas.ennreal_ofReal.aemeasurable]
  congr with y
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ ↦ statInfoFun_nonneg _ _ _)
    h_meas.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable, ENNReal.ofReal_toReal]
  refine (integrable_toReal_iff ?_ ?_).mp ?_
  · exact h_meas.comp (f := fun x ↦ (x, y)) (by fun_prop) |>.ennreal_ofReal.aemeasurable
  · exact .of_forall fun _ ↦ ENNReal.ofReal_ne_top
  · simp_rw [ENNReal.toReal_ofReal (statInfoFun_nonneg 1 _ _)]
    exact integrable_statInfoFun_rnDeriv 1 y μ ν

lemma fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous'
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f)
    (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) (h_ac : μ ≪ ν) :
    fDiv f μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ (fDiv (statInfoFun 1 x) μ ν).toReal) (curvatureMeasure f) := by
  rw [fDiv_ne_top_iff]
  simp only [h_ac, implies_true, and_true]
  have (x : 𝒳) : f ((∂μ/∂ν) x).toReal = (ENNReal.ofReal (f ((∂μ/∂ν) x).toReal)).toReal := by
    refine (ENNReal.toReal_ofReal ?_).symm
    rw [← integral_statInfoFun_curvatureMeasure' hf_cvx hf_cont hf_one hfderiv_one]
    exact integral_nonneg fun _ ↦ statInfoFun_nonneg 1 _ _
  have : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ (ENNReal.ofReal (f ((∂μ/∂ν) x).toReal)).toReal) ν := by
    simp_rw [← this]
  simp_rw [this, ← EReal.toReal_toENNReal fDiv_statInfoFun_nonneg]
  rw [integrable_toReal_iff]
  rotate_left
  · exact hf_cont.measurable.comp (μ.measurable_rnDeriv ν).ennreal_toReal
      |>.ennreal_ofReal.aemeasurable
  · exact .of_forall fun _ ↦ ENNReal.ofReal_ne_top
  rw [integrable_toReal_iff]
  rotate_left
  · exact (stronglyMeasurable_fDiv_statInfoFun μ ν).measurable.comp (f := fun x ↦ (1, x))
      (by fun_prop) |>.ereal_toENNReal.aemeasurable
  · exact .of_forall fun _ ↦ EReal.toENNReal_ne_top_iff.mpr fDiv_statInfoFun_ne_top
  rw [lintegral_f_rnDeriv_eq_lintegralfDiv_statInfoFun_of_absolutelyContinuous hf_cvx hf_cont
    hf_one hfderiv_one h_ac]

lemma fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (h_ac : μ ≪ ν) :
    fDiv f μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ (fDiv (statInfoFun 1 x) μ ν).toReal) (curvatureMeasure f) := by
  rw [fDiv_eq_fDiv_centeredFunction (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0)),
    EReal.add_ne_top_iff_of_ne_bot_of_ne_top]
  rotate_left
  · exact EReal.add_top_iff_ne_bot.mp rfl
  · exact Ne.symm (ne_of_beq_false rfl)
  rw [EReal.add_ne_top_iff_of_ne_bot_of_ne_top]
    <;> try {· simp [EReal.mul_ne_top, EReal.mul_ne_bot, measure_ne_top]}
  simp_rw [sub_eq_add_neg, ← neg_mul, mul_add, ← add_assoc]
  rw [fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous' _ _ (by ring) _ h_ac,
    curvatureMeasure_add_const, curvatureMeasure_add_linear, curvatureMeasure_add_const]
  · exact (hf_cvx.add_const _).add (const_mul_id (-rightDeriv f 1)) |>.add_const _
  · exact ((hf_cont.add continuous_const).add (continuous_mul_left _)).add continuous_const
  · have hf_diff := differentiableWithinAt_Ioi'
      (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0)) zero_lt_one
    rw [rightDeriv_add_const_apply, rightDeriv_add_linear_apply, rightDeriv_add_const_apply hf_diff,
      add_neg_cancel] <;> fun_prop


lemma integrable_f_rnDeriv_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (h_ac : μ ≪ ν) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ (fDiv (statInfoFun 1 x) μ ν).toReal) (curvatureMeasure f) := by
  rw [← fDiv_ne_top_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous hf_cvx hf_cont h_ac]
  simp [fDiv_ne_top_iff, h_ac]

lemma fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous'
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (hf_one : f 1 = 0)
    (hfderiv_one : rightDeriv f 1 = 0)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫ x, (fDiv (statInfoFun 1 x) μ ν).toReal ∂(curvatureMeasure f) := by
  classical
  rw [fDiv_of_absolutelyContinuous h_ac, if_pos h_int, EReal.coe_eq_coe_iff]
  simp_rw [fDiv_of_absolutelyContinuous h_ac, if_pos (integrable_statInfoFun_rnDeriv 1 _ _ _),
    EReal.toReal_coe,
    ← integral_statInfoFun_curvatureMeasure' hf_cvx hf_cont hf_one hfderiv_one]
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry :=
    stronglyMeasurable_statInfoFun.measurable.comp <|
      (measurable_const.prod_mk measurable_snd).prod_mk <|
      ((μ.measurable_rnDeriv ν).comp measurable_fst).ennreal_toReal
  have int_eq_lint : ∫ x, ∫ γ, statInfoFun 1 γ ((∂μ/∂ν) x).toReal ∂curvatureMeasure f ∂ν
      = (∫⁻ x, ∫⁻ γ, ENNReal.ofReal (statInfoFun 1 γ ((∂μ/∂ν) x).toReal)
        ∂curvatureMeasure f ∂ν).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    rotate_left
    · exact .of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
    · refine (StronglyMeasurable.integral_prod_left ?_).aestronglyMeasurable
      exact (measurable_swap_iff.mpr h_meas).stronglyMeasurable
    congr with x
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun y ↦ statInfoFun_nonneg _ _ _)
      h_meas.of_uncurry_left.stronglyMeasurable.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal <| (lintegral_ofReal_le_lintegral_nnnorm _).trans_lt ?_ |>.ne
    exact (integrable_statInfoFun 1 _).hasFiniteIntegral
  rw [int_eq_lint, lintegral_lintegral_swap h_meas.ennreal_ofReal.aemeasurable,
    integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact .of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
  · exact h_meas.stronglyMeasurable.integral_prod_left.aestronglyMeasurable
  congr with γ
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ ↦ statInfoFun_nonneg _ _ _)
    h_meas.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable, ENNReal.ofReal_toReal]
  have h_lt_top := (integrable_statInfoFun_rnDeriv 1 γ μ ν).hasFiniteIntegral
  simp_rw [HasFiniteIntegral, lt_top_iff_ne_top] at h_lt_top
  convert h_lt_top
  rw [← ENNReal.toReal_eq_toReal ENNReal.ofReal_ne_top ENNReal.coe_ne_top, toReal_coe_nnnorm,
    ENNReal.toReal_ofReal (statInfoFun_nonneg _ _ _),
    Real.norm_of_nonneg (statInfoFun_nonneg _ _ _)]

lemma fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫ x, (fDiv (statInfoFun 1 x) μ ν).toReal ∂(curvatureMeasure f)
      + f 1 * ν univ + rightDeriv f 1 * (μ univ - ν univ) := by
  rw [fDiv_eq_fDiv_centeredFunction (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0))]
  congr
  · rw [fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous'
      _ (by continuity) (by simp) _ _ h_ac]
    · simp_rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg, ← neg_mul, ← add_assoc,
        curvatureMeasure_add_const, curvatureMeasure_add_linear, curvatureMeasure_add_const]
    · simp_rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg, ← neg_mul]
      exact (hf_cvx.add_const _).add ((ConvexOn.const_mul_id _).add (convexOn_const _ convex_univ))
    · have hf_diff := differentiableWithinAt_Ioi'
        (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0)) zero_lt_one
      simp_rw [mul_sub, sub_eq_add_neg, neg_add, neg_neg, ← neg_mul, ← add_assoc]
      rw [rightDeriv_add_const_apply, rightDeriv_add_linear_apply,
        rightDeriv_add_const_apply hf_diff, add_neg_cancel]
      <;> fun_prop
    · exact (h_int.sub (integrable_const _)).sub
        ((Measure.integrable_toReal_rnDeriv.sub (integrable_const 1)).const_mul _)
  all_goals exact ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)

lemma fDiv_eq_lintegral_fDiv_statInfoFun_of_absolutelyContinuous [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂(curvatureMeasure f)
      + f 1 * ν univ + rightDeriv f 1 * (μ univ - ν univ) := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_eq_integral_fDiv_statInfoFun_of_absolutelyContinuous hf_cvx hf_cont h_int h_ac,
      integral_eq_lintegral_of_nonneg_ae]
    rotate_left
    · exact .of_forall <| fun _ ↦ EReal.toReal_nonneg fDiv_statInfoFun_nonneg
    · exact (stronglyMeasurable_fDiv_statInfoFun μ ν).measurable.comp (f := fun x ↦ (1, x))
        (by fun_prop) |>.ereal_toReal.aestronglyMeasurable
    simp_rw [← EReal.toENNReal_of_ne_top fDiv_statInfoFun_ne_top]
    rw [ENNReal.toReal_toEReal_of_ne_top]
    rw [integrable_f_rnDeriv_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous hf_cvx
      hf_cont h_ac] at h_int
    refine (integrable_toReal_iff ?_ ?_).mp ?_
    · exact (stronglyMeasurable_fDiv_statInfoFun μ ν).measurable.comp (f := fun x ↦ (1, x))
        (by fun_prop) |>.ereal_toENNReal.aemeasurable
    · exact .of_forall fun _ ↦ EReal.toENNReal_ne_top_iff.mpr fDiv_statInfoFun_ne_top
    simp_rw [EReal.toReal_toENNReal fDiv_statInfoFun_nonneg, h_int]
  · classical
    rw [fDiv_of_absolutelyContinuous h_ac, if_neg h_int]
    convert (EReal.top_add_of_ne_bot ?_).symm
    swap
    · simp [sub_eq_add_neg, measure_ne_top, EReal.add_ne_top, EReal.add_ne_bot, EReal.mul_ne_bot]
    convert EReal.top_add_of_ne_bot ?_
    swap; · simp [measure_ne_top, EReal.mul_ne_bot]
    simp_rw [EReal.coe_ennreal_eq_top_iff]
    have h := integrable_f_rnDeriv_iff_integrable_fDiv_statInfoFun_of_absolutelyContinuous
      hf_cvx hf_cont h_ac |>.mpr.mt h_int
    contrapose! h
    simp_rw [← EReal.toReal_toENNReal fDiv_statInfoFun_nonneg]
    refine (integrable_toReal_iff ?_ ?_).mpr h
    · exact (stronglyMeasurable_fDiv_statInfoFun μ ν).measurable.comp (f := fun x ↦ (1, x))
        (by fun_prop) |>.ereal_toENNReal.aemeasurable
    · exact .of_forall fun _ ↦ EReal.toENNReal_ne_top_iff.mpr fDiv_statInfoFun_ne_top

lemma lintegral_statInfoFun_one_zero (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    ∫⁻ x, ENNReal.ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f
      = (f 0).toEReal - f 1 + rightDeriv f 1 := by
  norm_cast
  have := convex_taylor hf_cvx hf_cont (a := 1) (b := 0)
  simp only [zero_sub, mul_neg, mul_one, sub_neg_eq_add] at this
  rw [this, intervalIntegral.integral_of_ge (zero_le_one' _), integral_neg, neg_neg,
    ← ofReal_integral_eq_lintegral_ofReal _ (.of_forall fun x ↦ statInfoFun_nonneg 1 x 0)]
  rotate_left
  · refine Integrable.mono' (g := (Ioc 0 1).indicator 1) ?_
      measurable_statInfoFun2.aestronglyMeasurable ?_
    · exact IntegrableOn.integrable_indicator
        (integrableOn_const.mpr (Or.inr measure_Ioc_lt_top)) measurableSet_Ioc
    · simp_rw [Real.norm_of_nonneg (statInfoFun_nonneg 1 _ 0),
        statInfoFun_of_one_of_right_le_one zero_le_one, sub_zero]
      exact .of_forall fun x ↦ Set.indicator_le_indicator' fun hx ↦ hx.2
  rw [EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg_of_ae <| .of_forall
    fun x ↦ statInfoFun_nonneg 1 x 0), ← integral_indicator measurableSet_Ioc]
  simp_rw [statInfoFun_of_one_of_right_le_one zero_le_one, sub_zero]

lemma fDiv_eq_lintegral_fDiv_statInfoFun_of_mutuallySingular [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (h_ms : μ ⟂ₘ ν) :
    fDiv f μ ν = ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂(curvatureMeasure f)
      + f 1 * ν univ + rightDeriv f 1 * (μ univ - ν univ) := by
  have hf_cvx' : ConvexOn ℝ (Ici 0) f := (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0))
  have h1 : ∫⁻ x, (statInfoFun 1 x 0 * (ν univ).toEReal
        + derivAtTop (statInfoFun 1 x) * μ univ).toENNReal ∂curvatureMeasure f
      = (∫⁻ x, ENNReal.ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f) * ν univ
        + (∫⁻ x, (derivAtTop (statInfoFun 1 x)).toENNReal ∂curvatureMeasure f) * μ univ := by
    rw [← lintegral_mul_const _ (Measurable.ennreal_ofReal measurable_statInfoFun2),
      ← lintegral_mul_const _]
    swap
    · simp_rw [derivAtTop_statInfoFun_eq]
      refine (Measurable.ite (.const _) ?_ ?_).coe_real_ereal.ereal_toENNReal <;>
      · refine Measurable.ite (measurableSet_le (fun _ a ↦ a) ?_) ?_ ?_ <;> exact measurable_const
    rw [← lintegral_add_left]
    swap; · exact measurable_statInfoFun2.ennreal_ofReal.mul_const _
    congr with x
    rw [EReal.toENNReal_add]
    rotate_left
    · exact mul_nonneg (EReal.coe_nonneg.mpr (statInfoFun_nonneg 1 x 0))
        (EReal.coe_ennreal_nonneg _)
    · exact mul_nonneg (derivAtTop_statInfoFun_nonneg 1 x) (EReal.coe_ennreal_nonneg _)
    rw [EReal.toENNReal_mul (EReal.coe_nonneg.mpr <| statInfoFun_nonneg 1 x 0),
      EReal.toENNReal_mul (derivAtTop_statInfoFun_nonneg 1 x)]
    simp [-statInfoFun_of_one]
  have h2 : ∫⁻ x, (derivAtTop (statInfoFun 1 x)).toENNReal ∂curvatureMeasure f
      = (derivAtTop f - rightDeriv f 1).toENNReal := by
    calc
      _ = curvatureMeasure f (Ioi 1) := by
        simp_rw [derivAtTop_statInfoFun_eq, ← lintegral_indicator_one measurableSet_Ioi]
        congr with x
        by_cases h : x ∈ Ioi 1
        · simpa [h]
        · simp [h, show x ≤ 1 from le_of_not_lt h]
      _ = (derivAtTop f - rightDeriv f 1).toENNReal := by
        rw [curvatureMeasure_of_convexOn hf_cvx]
        by_cases h_top : derivAtTop f = ⊤
        · rw [h_top, EReal.top_sub_coe, EReal.toENNReal_top,
            StieltjesFunction.measure_Ioi_of_tendsto_atTop_atTop]
          exact hf_cvx'.derivAtTop_eq_top_iff.mp h_top
        · lift (derivAtTop f) to ℝ using ⟨h_top, hf_cvx'.derivAtTop_ne_bot⟩ with x hx
          rw [StieltjesFunction.measure_Ioi _ ?_ 1 (l := x)]
          · norm_cast
          exact (hx ▸ hf_cvx'.tendsto_toReal_derivAtTop (hx ▸ h_top) :)
  simp_rw [fDiv_of_mutuallySingular h_ms, h1]
  push_cast
  rw [lintegral_statInfoFun_one_zero hf_cvx hf_cont, h2, EReal.coe_toENNReal]
  swap
  · rw [EReal.sub_nonneg (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    exact rightDeriv_le_derivAtTop hf_cvx' zero_lt_one
  simp_rw [sub_eq_add_neg, ← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top ν _),
    ← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top μ _),
    EReal.add_mul_coe_of_nonneg ENNReal.toReal_nonneg, ← EReal.coe_neg (ν univ).toReal,
    ← EReal.coe_add, ← EReal.coe_mul _ (_ + _), mul_add, EReal.coe_add, neg_mul, ← EReal.coe_mul,
    mul_neg, EReal.coe_neg, add_assoc]
  congr
  simp_rw [add_comm (rightDeriv f 1 * (ν _).toReal).toEReal, add_assoc,
    add_comm _ (rightDeriv f 1 * _).toEReal, ← add_assoc, ← sub_eq_add_neg,
    EReal.add_sub_cancel_right, sub_eq_add_neg, add_assoc, add_comm _ (_ + (_ + (_ + _))),
    add_comm (f 1 * _).toEReal, ← add_assoc, ← sub_eq_add_neg, EReal.add_sub_cancel_right,
    sub_eq_add_neg, add_assoc, add_comm (-(rightDeriv f 1 * _).toEReal), ← add_assoc,
    ← sub_eq_add_neg, EReal.add_sub_cancel_right]

lemma fDiv_eq_lintegral_fDiv_statInfoFun [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) :
    fDiv f μ ν = ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂(curvatureMeasure f)
      + f 1 * ν univ + rightDeriv f 1 * (μ univ - ν univ) := by
  rw [fDiv_eq_add_withDensity_singularPart _ _ (hf_cvx.subset (fun _ _ ↦ trivial) (convex_Ici 0)),
    fDiv_eq_lintegral_fDiv_statInfoFun_of_mutuallySingular hf_cvx hf_cont
    (μ.mutuallySingular_singularPart ν), fDiv_eq_lintegral_fDiv_statInfoFun_of_absolutelyContinuous
    hf_cvx hf_cont (withDensity_absolutelyContinuous ν (∂μ/∂ν))]
  have h1 : ∫⁻ x, (fDiv (statInfoFun 1 x) μ ν).toENNReal ∂curvatureMeasure f
      = ∫⁻ x, (fDiv (statInfoFun 1 x) (ν.withDensity (∂μ/∂ν)) ν).toENNReal ∂curvatureMeasure f
        + ∫⁻ x, (fDiv (statInfoFun 1 x) (μ.singularPart ν) ν).toENNReal ∂curvatureMeasure f
        - (∫⁻ x, .ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f : EReal) * (ν univ).toReal := by
    have h_nonneg (x : ℝ) : 0 ≤ fDiv (statInfoFun 1 x) μ ν := fDiv_statInfoFun_nonneg
    simp_rw [fDiv_eq_add_withDensity_singularPart μ ν ((convexOn_statInfoFun 1 _).subset
      (fun _ _ ↦ trivial) (convex_Ici 0))] at h_nonneg ⊢
    rw_mod_cast [← lintegral_add_left]
    swap; · exact ((stronglyMeasurable_fDiv_statInfoFun (ν.withDensity (∂μ/∂ν)) ν).measurable.comp
      (by fun_prop) (f := fun x ↦ (1, x))).ereal_toENNReal
    simp_rw [← EReal.toENNReal_add fDiv_statInfoFun_nonneg fDiv_statInfoFun_nonneg]
    have h_ne_top : (∫⁻ x, .ofReal (statInfoFun 1 x 0) ∂curvatureMeasure f) * ν univ ≠ ⊤ := by
      refine ENNReal.mul_ne_top (lt_top_iff_ne_top.mp ?_) (measure_ne_top ν _)
      calc
        _ ≤ ∫⁻ x, (Ioc 0 1).indicator 1 x ∂curvatureMeasure f := by
          simp_rw [statInfoFun_of_one_of_right_le_one zero_le_one, sub_zero]
          refine lintegral_mono (le_indicator ?_ ?_) <;> simp_all
        _ < _ := by
          rw [lintegral_indicator_one measurableSet_Ioc]
          exact measure_Ioc_lt_top
    have h_le (x : ℝ) : .ofReal (statInfoFun 1 x 0) * ν univ
        ≤ (fDiv (statInfoFun 1 x) (ν.withDensity (∂μ/∂ν)) ν
          + fDiv (statInfoFun 1 x) (μ.singularPart ν) ν).toENNReal := by
      rw [← EReal.real_coe_toENNReal, ← EReal.toENNReal_coe (x := ν _),
        ← EReal.toENNReal_mul (EReal.coe_nonneg.mpr <| statInfoFun_nonneg 1 x 0)]
      refine EReal.toENNReal_le_toENNReal <| (EReal.sub_nonneg ?_ ?_).mp (h_nonneg x)
        <;> simp [EReal.mul_ne_top, EReal.mul_ne_bot, measure_ne_top ν univ]
    rw [ENNReal.toReal_toEReal_of_ne_top (measure_ne_top ν _), ← EReal.coe_ennreal_mul,
      ← ENNReal.toEReal_sub h_ne_top]
    swap
    · exact lintegral_mul_const' _ _ (measure_ne_top ν _) ▸ lintegral_mono h_le
    rw [← lintegral_mul_const' _ _ (measure_ne_top ν _),
      ← lintegral_sub (measurable_statInfoFun2.ennreal_ofReal.mul_const _)
      (lintegral_mul_const' _ _ (measure_ne_top ν _) ▸ h_ne_top) (.of_forall h_le)]
    congr with x
    rw [EReal.toENNReal_sub (mul_nonneg (EReal.coe_nonneg.mpr (statInfoFun_nonneg 1 x 0))
      (EReal.coe_ennreal_nonneg _)),
      EReal.toENNReal_mul (EReal.coe_nonneg.mpr (statInfoFun_nonneg 1 x 0)), EReal.toENNReal_coe]
    congr
  simp_rw [h1, lintegral_statInfoFun_one_zero hf_cvx hf_cont, sub_eq_add_neg, add_assoc]
  congr 1
  simp_rw [add_comm (- (((f 0).toEReal + _) * _)), add_comm (∫⁻ _, _ ∂_).toEReal _, ← add_assoc,
    ← ENNReal.toReal_toEReal_of_ne_top (measure_ne_top _ _)]
  norm_cast
  ring_nf
  simp_rw [sub_eq_add_neg, mul_assoc, ← mul_neg, ← mul_add]
  congr 1
  nth_rw 3 [μ.haveLebesgueDecomposition_add ν]
  rw [Measure.coe_add, Pi.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring_nf

end StatInfoFun

end ProbabilityTheory
