module

public import AffineFK.UnweightedSobolevGraph
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.Moments.Variance

/-!
# Exact directional translation estimate on smooth functions

The line fundamental theorem and probability-space Cauchy--Schwarz retain
only the directional derivative. This avoids the dimension loss produced
by bounding it with the full gradient norm before Gaussian averaging.
Reuse: Mathlib FTC and variance nonnegativity; the line proof follows the
actual argument in Adam Benenson's attributed translation estimate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace

theorem smooth_directional_translation_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (x z : E) :
    (f (x + z) - f x)^2 ≤
      ∫ t in Icc (0 : ℝ) 1, (⟪gradient f (x + t • z), z⟫)^2 := by
  let d : ℝ → ℝ := fun t => fderiv ℝ f (x + t • z) z
  have hd : Continuous d := by
    exact ((hf.continuous_fderiv (by simp)).comp
      (show Continuous (fun t : ℝ => x + t • z) by fun_prop)).clm_apply continuous_const
  have hderiv (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • z)) (d t) t := by
    have hline : HasDerivAt (fun s : ℝ => x + s • z) z t := by
      simpa only [one_smul] using! ((hasDerivAt_id t).smul_const z).const_add x
    exact (hf.differentiable one_ne_zero |>.differentiableAt.hasFDerivAt).comp_hasDerivAt t hline
  have hFTC : (∫ t in Icc (0 : ℝ) 1, d t) = f (x + z) - f x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simpa using! intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ht => hderiv t) (hd.intervalIntegrable 0 1)
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  have hdLp : MemLp d 2 μ := by
    apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mpr
    exact (hd.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hvar := variance_nonneg d μ
  rw [variance_eq_sub hdLp] at hvar
  have hsq : (∫ t in Icc (0 : ℝ) 1, d t)^2 ≤
      ∫ t in Icc (0 : ℝ) 1, (d t)^2 := by
    change (∫ t, d t ∂μ)^2 ≤ ∫ t, (d t)^2 ∂μ
    simpa only [Pi.pow_apply] using sub_nonneg.mp hvar
  rw [hFTC] at hsq
  convert hsq using 1
  congr 1
  funext t
  rw [inner_gradient_left]

end AffineFKProof
