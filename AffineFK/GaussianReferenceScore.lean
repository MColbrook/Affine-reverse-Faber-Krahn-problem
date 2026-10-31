module

public import AffineFK.StandardGaussianDensity
public import AffineFK.DensityRatio
public import AffineFK.GaussianRelativeScore
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The actual Gaussian reference measure and a smooth relative density

Mathlib's standard Gaussian is the measure with the positive smooth
coordinate-product density. Its logarithmic gradient is minus the identity.
For a positive smooth Lebesgue density rho, rho divided by this fixed density
is a smooth representative of the actual Radon--Nikodym derivative. The
derivative assertion concerns this representative, not an arbitrary
almost-everywhere version of rnDeriv.

The Gaussian densities and measure identification reuse Mathlib's Gaussian
development, the logarithmic product identity and inner-product-space norm
derivative. The Radon--Nikodym representative reuses Mathlib's withDensity
and rnDeriv_withDensity theorems (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ContDiff RealInnerProductSpace

theorem log_standardGaussianDensity (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    Real.log (standardGaussianDensity n x) =
      (n : ℝ) * Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - ‖x‖ ^ 2 / 2 := by
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ ≠ 0 := by positivity
  calc
    _ = ∑ i : Fin n, (Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - (x i) ^ 2 / 2) := by
      rw [standardGaussianDensity, Real.log_prod (fun i _ =>
        (gaussianPDFReal_pos 0 1 (x i) one_ne_zero).ne')]
      apply Finset.sum_congr rfl
      intro i _
      simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
      rw [Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq]

theorem gradient_log_standardGaussianDensity
    (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => Real.log (standardGaussianDensity n y)) x = -x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ)).const_sub
    ((n : ℝ) * Real.log ((Real.sqrt (2 * Real.pi))⁻¹))
  have hd : HasFDerivAt (fun y => Real.log (standardGaussianDensity n y))
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (-x)) x := by
    convert h using 1
    · funext y
      rw [log_standardGaussianDensity]
      ring
    · ext y
      simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, inner_neg_left]
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

theorem gaussian_relative_density_smooth
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (fun x => ρ x / standardGaussianDensity n x) :=
  hρ.div (standardGaussianDensity_smooth n) (fun x => (standardGaussianDensity_pos n x).ne')

theorem gaussian_relative_density_pos
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρpos : ∀ x, 0 < ρ x)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 < ρ x / standardGaussianDensity n x :=
  div_pos (hρpos x) (standardGaussianDensity_pos n x)

theorem gaussian_relative_density_withDensity
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Continuous ρ) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).withDensity
      (fun x => ENNReal.ofReal (ρ x / standardGaussianDensity n x)) = densityMeasure n ρ := by
  rw [stdGaussian_eq_densityMeasure]
  exact densityMeasure_withDensity_ratio n ρ (standardGaussianDensity n) hρ
    (standardGaussianDensity_smooth n).continuous (standardGaussianDensity_pos n)

theorem densityMeasure_absolutelyContinuous_stdGaussian
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Continuous ρ) :
    densityMeasure n ρ ≪ stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [← gaussian_relative_density_withDensity n ρ hρ]
  exact withDensity_absolutelyContinuous _ _

theorem gaussian_relative_density_rnDeriv
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Continuous ρ) :
    (densityMeasure n ρ).rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n)))
      =ᵐ[stdGaussian (EuclideanSpace ℝ (Fin n))]
      (fun x => ENNReal.ofReal (ρ x / standardGaussianDensity n x)) := by
  letI : IsProbabilityMeasure (densityMeasure n (standardGaussianDensity n)) := by
    rw [← stdGaussian_eq_densityMeasure]
    infer_instance
  simpa only [stdGaussian_eq_densityMeasure n] using
    densityMeasure_ratio_rnDeriv n ρ (standardGaussianDensity n) hρ
      (standardGaussianDensity_smooth n).continuous (standardGaussianDensity_pos n)

theorem gradient_log_gaussian_relative_density
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => Real.log (ρ y / standardGaussianDensity n y)) x =
      gaussianRelativeScore n ρ x := by
  rw [gradient_log_density_ratio n ρ (standardGaussianDensity n) hρ
    (standardGaussianDensity_smooth n) hρpos (standardGaussianDensity_pos n),
    gradient_log_standardGaussianDensity]
  simp only [gaussianRelativeScore, sub_neg_eq_add]

end AffineFKProof
