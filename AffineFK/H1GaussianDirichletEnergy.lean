module

public import AffineFK.H1GaussianDirectionalScaled
public import AffineFK.H1GaussianDirichletForm

/-!
# The dimension-free Gaussian form upper bound on genuine H1

The same actual Lebesgue L2 function and its completed weak gradient enter
the Gaussian translation identity and the exact covariance calculation.
The comparison is valid for signed functions and every dimension.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

theorem h1Gaussian_translation_difference_sq_le (n : ℕ) (b : ℝ)
    (v : unweightedSobolevGraph n) :
    (∫ u, ‖bridgeL2Translate n (b • u) (unweightedValue n v) - unweightedValue n v‖^2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ b^2 * ‖unweightedGradient n v‖^2 := by
  have hD := (gaussianL2Average_difference_sq_identity n b (unweightedValue n v)).1
  obtain ⟨hR, hmoment⟩ :=
    l2DirectionalPairing_scaled_gaussian_second_moment n b (unweightedGradient n v)
  rw [← hmoment]
  exact integral_mono hD hR (fun u => h1_directional_translation_norm_sq_le n v (b • u))

theorem h1GaussianDirichletForm_le_gradient_energy (n : ℕ) (h : ℝ) (hh : 0 < h)
    (v : unweightedSobolevGraph n) :
    h1GaussianDirichletForm n h (unweightedValue n v) ≤ ‖unweightedGradient n v‖^2 := by
  rw [h1GaussianDirichletForm_eq_translation_integral]
  calc
    _ ≤ h⁻¹ * ((Real.sqrt h)^2 * ‖unweightedGradient n v‖^2) :=
      mul_le_mul_of_nonneg_left (h1Gaussian_translation_difference_sq_le n (Real.sqrt h) v)
        (inv_nonneg.mpr hh.le)
    _ = _ := by
      rw [Real.sq_sqrt hh.le, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]

theorem h1GaussianDirichletForm_nonneg (n : ℕ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    0 ≤ h1GaussianDirichletForm n h f := by
  rw [h1GaussianDirichletForm_eq_translation_integral]
  exact mul_nonneg (inv_nonneg.mpr hh.le) (integral_nonneg fun _ => sq_nonneg _)

theorem gaussianL2Average_sub_norm_sq_le_form (n : ℕ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖bridgeGaussianL2Average n (Real.sqrt h) f - f‖^2 ≤ h * h1GaussianDirichletForm n h f := by
  have hQ := bridgeGaussianL2Average_norm_le n (Real.sqrt h) f
  have hQsq := pow_le_pow_left₀ (norm_nonneg _) hQ 2
  have hraw : ‖bridgeGaussianL2Average n (Real.sqrt h) f - f‖^2 ≤
      2 * (‖f‖^2 - ⟪f, bridgeGaussianL2Average n (Real.sqrt h) f⟫) := by
    rw [norm_sub_sq_real, real_inner_comm]
    nlinarith
  apply hraw.trans_eq
  have hc : h * (2 / h) = 2 := by field_simp
  change 2 * _ = h * ((2 / h) * _)
  rw [← mul_assoc, hc]

end AffineFKProof
