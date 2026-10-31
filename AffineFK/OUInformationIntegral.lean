module

public import AffineFK.EntropyIntegral
public import AffineFK.OrnsteinUhlenbeckScales
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The actual time-integral estimate in the second-order HSI argument

The substitution z=1-exp(-2t) is proved for the genuine interval integral.
The earlier scalar HSI estimate then gives the exact square-root constant,
including zero information and zero tensor energy. Substitution reuses
Mathlib's one-dimensional Jacobian/FTC proofs (Yury Kudryashov, Patrick
Massot, Sebastien Gouezel and contributors; Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Filter intervalIntegral
open scoped Interval

def ouInformationEnvelope (A B t : ℝ) : ℝ :=
  min (Real.exp (-2 * t) * A)
    ((2 * Real.exp (-6 * t) / (1 - Real.exp (-2 * t)) ^ 2) * B)

theorem ouInformationEnvelope_intervalIntegrable (A B s t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IntervalIntegrable (ouInformationEnvelope A B) volume s t := by
  apply ((show Continuous (fun r : ℝ => Real.exp (-2 * r) * A) by fun_prop).intervalIntegrable s t).mono_fun'
  · unfold ouInformationEnvelope
    fun_prop
  · filter_upwards [] with r
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ ouInformationEnvelope A B r from
      le_min (mul_nonneg (Real.exp_pos _).le hA)
        (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (sq_nonneg _)) hB))]
    exact min_le_left _ _

theorem ouInformationEnvelope_time_integral_bound (A B s t : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ r in s..t, ouInformationEnvelope A B r) ≤ Real.sqrt 2 * Real.sqrt B * Real.sqrt A := by
  let Z : ℝ → ℝ := fun r => 1 - Real.exp (-2 * r)
  let F : ℝ → ℝ := fun z => min A (2 * B * (1 - z) ^ 2 / z ^ 2)
  have hZ (r : ℝ) : HasDerivAt Z (2 * Real.exp (-2 * r)) r := by
    have he : HasDerivAt (fun u : ℝ => Real.exp (-2 * u)) (-2 * Real.exp (-2 * r)) r := by
      convert ((hasDerivAt_id r).const_mul (-2 : ℝ)).exp using 1 <;> simp only [id_eq] <;> ring
    convert he.const_sub 1 using 1 <;> ring
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := s) (b := t) (f := Z) (f' := fun r => 2 * Real.exp (-2 * r)) (g := F)
    (by fun_prop) (fun r _ => hZ r) (fun r _ => by positivity)
  have hpoint (r : ℝ) (hr : 0 ≤ r) :
      ouInformationEnvelope A B r = (1 / 2 : ℝ) * (F (Z r) * (2 * Real.exp (-2 * r))) := by
    by_cases hzero : r = 0
    · subst r
      simp [ouInformationEnvelope, F, Z, min_eq_right hA]
    have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
    have hexp : Real.exp (-2 * r) ^ 3 = Real.exp (-6 * r) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hz : 1 - Real.exp (-2 * r) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -2 * r < 0)
      linarith
    change _ = (1 / 2 : ℝ) * (min A (2 * B * (1 - (1 - Real.exp (-2 * r))) ^ 2 /
      (1 - Real.exp (-2 * r)) ^ 2) * (2 * Real.exp (-2 * r)))
    rw [show 1 - (1 - Real.exp (-2 * r)) = Real.exp (-2 * r) by ring]
    rw [show (1 / 2 : ℝ) * (min A _ * (2 * Real.exp (-2 * r))) =
      Real.exp (-2 * r) * min A _ by ring,
      mul_min_of_nonneg _ _ (Real.exp_pos (-2 * r)).le]
    unfold ouInformationEnvelope
    congr 1
    rw [← hexp]
    field_simp [hz]
  have htime : (∫ r in s..t, ouInformationEnvelope A B r) =
      (1 / 2 : ℝ) * (∫ z in Z s..Z t, F z) := by
    calc
      _ = ∫ r in s..t, (1 / 2 : ℝ) * (F (Z r) * (2 * Real.exp (-2 * r))) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hst] at hr
        exact hpoint r (hs.trans hr.1)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
        simpa only [Function.comp_def] using congrArg (fun u : ℝ => (1 / 2 : ℝ) * u) hsubst
  have hFnonneg (z : ℝ) : 0 ≤ F z :=
    le_min hA (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) (sq_nonneg _)) (sq_nonneg _))
  have hFint : IntervalIntegrable F volume 0 1 := by
    apply (intervalIntegrable_const (c := A)).mono_fun'
    · exact (measurable_const.min
        ((measurable_const.mul ((measurable_const.sub measurable_id).pow_const 2)).div
          (measurable_id.pow_const 2))).aestronglyMeasurable
    · filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg z)]
      exact min_le_left _ _
  have hZs : 0 ≤ Z s := by
    dsimp [Z]
    have := Real.exp_le_one_iff.mpr (by linarith : -2 * s ≤ 0)
    linarith
  have hZst : Z s ≤ Z t := by
    dsimp [Z]
    have := Real.exp_le_exp.mpr (by linarith : -2 * t ≤ -2 * s)
    linarith
  have hZt : Z t ≤ 1 := by dsimp [Z]; linarith [Real.exp_pos (-2 * t)]
  rw [htime]
  calc
    _ ≤ (1 / 2 : ℝ) * (∫ z in (0 : ℝ)..1, F z) :=
      mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval hZs hZst hZt
        (Filter.Eventually.of_forall hFnonneg) hFint) (by norm_num)
    _ ≤ _ := by
      simpa only [F, Real.sq_sqrt hB] using
        hsi_scalar_integral_bound A (Real.sqrt B) hA (Real.sqrt_nonneg B)

end AffineFKProof
