module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# The scalar integral in the entropy--Stein estimate

This is the actual Lebesgue interval integral in the final step of the HSI
argument, rather than an assumed bound on its value. The OU dissipation formula
and the preceding change of variable are separate outstanding obligations.
The integral of a negative integer power is reused from Mathlib's integration
library (Benjamin Davidson and the contributors credited in its source).
-/

public section
namespace AffineFKProof
open MeasureTheory Set intervalIntegral
open scoped Interval

/-- The minimum removes the nonintegrable singularity at zero. -/
theorem intervalIntegrable_min_const_div_sq
    (I B a b : ℝ) (hI : 0 ≤ I) (hB : 0 ≤ B) :
    IntervalIntegrable (fun z : ℝ => min I (B / z ^ 2)) volume a b := by
  refine (intervalIntegrable_const (c := I)).mono_fun' ?_ ?_
  · exact (measurable_const.min
      (measurable_const.div (measurable_id.pow_const 2))).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hI (div_nonneg hB (sq_nonneg z)))]
    exact min_le_left _ _

/-- Splitting at any positive threshold bounds the true singular-minimum
integral by a constant part and an integrable reciprocal-square tail. -/
theorem entropy_integral_split_bound
    (I B r : ℝ) (hI : 0 ≤ I) (hB : 0 ≤ B)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    (∫ z : ℝ in 0..1, min I (B / z ^ 2)) ≤ I * r + B / r := by
  have hf0r := intervalIntegrable_min_const_div_sq I B 0 r hI hB
  have hfr1 := intervalIntegrable_min_const_div_sq I B r 1 hI hB
  have hz : (0 : ℝ) ∉ [[r, 1]] := notMem_uIcc_of_lt hr (by norm_num)
  have hfun : (fun z : ℝ => B / z ^ 2) = (fun z : ℝ => B * z ^ (-2 : ℤ)) := by
    funext z
    simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv]
  have hg : IntervalIntegrable (fun z : ℝ => B / z ^ 2) volume r 1 := by
    rw [hfun]
    exact (intervalIntegrable_zpow (Or.inr hz)).const_mul B
  have hp : (∫ z : ℝ in r..1, z ^ (-2 : ℤ)) = r⁻¹ - 1 := by
    rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num
    ring
  have htail : (∫ z : ℝ in r..1, B / z ^ 2) = B * (r⁻¹ - 1) := by
    rw [hfun, intervalIntegral.integral_const_mul, hp]
  have hleft := intervalIntegral.integral_mono_on hr.le hf0r
    (intervalIntegrable_const (c := I)) (fun z _hz => min_le_left I (B / z ^ 2))
  have hright := intervalIntegral.integral_mono_on hr1 hfr1 hg
    (fun z _hz => min_le_right I (B / z ^ 2))
  rw [intervalIntegral.integral_const] at hleft
  rw [htail] at hright
  rw [← intervalIntegral.integral_add_adjacent_intervals hf0r hfr1]
  simp only [sub_zero, smul_eq_mul] at hleft
  rw [div_eq_mul_inv]
  nlinarith

/-- Optimising the split threshold; the zero cases require no division. -/
theorem entropy_integral_square_bound
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ z : ℝ in 0..1, min (a ^ 2) (b ^ 2 / z ^ 2)) ≤ 2 * a * b := by
  by_cases ha0 : a = 0
  · have hf : (fun z : ℝ => min (a ^ 2) (b ^ 2 / z ^ 2)) = fun _ => 0 := by
      funext z
      rw [ha0, zero_pow (show 2 ≠ 0 by decide)]
      exact min_eq_left (div_nonneg (sq_nonneg b) (sq_nonneg z))
    rw [hf, intervalIntegral.integral_zero, ha0]
    simp only [mul_zero, zero_mul, le_refl]
  by_cases hb0 : b = 0
  · have hf : (fun z : ℝ => min (a ^ 2) (b ^ 2 / z ^ 2)) = fun _ => 0 := by
      funext z
      rw [hb0, zero_pow (show 2 ≠ 0 by decide), zero_div]
      exact min_eq_right (sq_nonneg a)
    rw [hf, intervalIntegral.integral_zero, hb0]
    simp only [mul_zero, le_refl]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases hsmall : b / a ≤ 1
  · have hsplit := entropy_integral_split_bound (a ^ 2) (b ^ 2) (b / a)
      (sq_nonneg a) (sq_nonneg b) (div_pos hbp hap) hsmall
    have hid : a ^ 2 * (b / a) + b ^ 2 / (b / a) = 2 * a * b := by
      field_simp
      ring
    rwa [hid] at hsplit
  · have hconst := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
      (by norm_num) (intervalIntegrable_min_const_div_sq (a ^ 2) (b ^ 2) 0 1
        (sq_nonneg a) (sq_nonneg b))
      (intervalIntegrable_const (c := a ^ 2))
      (fun z _hz => min_le_left (a ^ 2) (b ^ 2 / z ^ 2))
    have hab : a < b := (one_lt_div hap).mp (lt_of_not_ge hsmall)
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hconst
    nlinarith

/-- The exact constant in the manuscript's scalar HSI integral estimate. -/
theorem entropy_integral_bound
    (I s : ℝ) (hI : 0 ≤ I) (hs : 0 ≤ s) :
    (1 / 2 : ℝ) * (∫ z : ℝ in 0..1, min I (2 * s ^ 2 / z ^ 2)) ≤
      Real.sqrt 2 * s * Real.sqrt I := by
  have h := entropy_integral_square_bound (Real.sqrt I) (Real.sqrt 2 * s)
    (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hs)
  have hb : (Real.sqrt 2 * s) ^ 2 = 2 * s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.sq_sqrt hI, hb] at h
  nlinarith

/-- Removing the factor at most one in the actual pre-optimisation integral,
with integrability proved for both sides. -/
theorem entropy_integral_remove_factor
    (I B : ℝ) (hI : 0 ≤ I) (hB : 0 ≤ B) :
    (∫ z : ℝ in 0..1, min I (B * (1 - z) ^ 2 / z ^ 2)) ≤
      ∫ z : ℝ in 0..1, min I (B / z ^ 2) := by
  have hf : IntervalIntegrable
      (fun z : ℝ => min I (B * (1 - z) ^ 2 / z ^ 2)) volume 0 1 := by
    refine (intervalIntegrable_const (c := I)).mono_fun' ?_ ?_
    · exact (measurable_const.min
        ((measurable_const.mul ((measurable_const.sub measurable_id).pow_const 2)).div
          (measurable_id.pow_const 2))).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg
        (le_min hI (div_nonneg (mul_nonneg hB (sq_nonneg _)) (sq_nonneg z)))]
      exact min_le_left _ _
  apply intervalIntegral.integral_mono_on (by norm_num) hf
    (intervalIntegrable_min_const_div_sq I B 0 1 hI hB)
  intro z hz
  apply min_le_min_left
  apply div_le_div_of_nonneg_right _ (sq_nonneg z)
  have hsq : (1 - z) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hB

/-- The final integral estimate in the HSI argument, including vanishing
information or tensor norm. -/
theorem hsi_scalar_integral_bound
    (I s : ℝ) (hI : 0 ≤ I) (hs : 0 ≤ s) :
    (1 / 2 : ℝ) *
        (∫ z : ℝ in 0..1, min I (2 * s ^ 2 * (1 - z) ^ 2 / z ^ 2)) ≤
      Real.sqrt 2 * s * Real.sqrt I := by
  calc
    _ ≤ (1 / 2 : ℝ) * (∫ z : ℝ in 0..1, min I (2 * s ^ 2 / z ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (entropy_integral_remove_factor I (2 * s ^ 2) hI
          (mul_nonneg (by norm_num) (sq_nonneg s))) (by norm_num)
    _ ≤ _ := entropy_integral_bound I s hI hs

end AffineFKProof
