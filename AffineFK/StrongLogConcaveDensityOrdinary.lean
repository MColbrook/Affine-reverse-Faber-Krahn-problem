module

public import AffineFK.GaussianPositionPoincare
public import AffineFK.GaussianLogConcavity

/-! A pointwise quadratic-exponential tilt gives ordinary log-concavity.
The genuine Gaussian density supplies the inverse tilt; normalization is
a positive constant, so support and zero density values are retained. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem strongLogConcaveDensity_logConcave (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal
      (ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)))) :
    LogConcaveDensity (fun x => ENNReal.ofReal (ρ x)) := by
  let c := Real.exp ((n : ℝ) * Real.log ((Real.sqrt (2 * Real.pi))⁻¹))
  have hc : 0 < c := Real.exp_pos _
  have hprod := logConcaveDensity_mul _ _ hlc (logConcaveDensity_standardGaussian n)
  have h := logConcaveDensity_mul (fun _ : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal c⁻¹)
    _ (logConcaveDensity_const _) hprod
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal c⁻¹ *
      (ENNReal.ofReal (ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)) *
        ENNReal.ofReal (standardGaussianDensity n x))) =
      (fun x => ENNReal.ofReal (ρ x)) := by
    funext x
    rw [← ENNReal.ofReal_mul (mul_nonneg (hρ0 x) (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
    congr 1
    calc
      _ = c⁻¹ * (ρ x * (standardGaussianDensity n x *
          Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))) := by ring
      _ = ρ x := by rw [gaussianPosition_gaussian_quadratic_tilt]; change c⁻¹ * (ρ x * c) = _; field_simp
  rwa [heq] at h

theorem gaussianPositionRestrictedDensity_logConcave (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Convex ℝ K) :
    LogConcaveDensity (fun x => ENNReal.ofReal (gaussianPositionRestrictedDensity n K x)) :=
  strongLogConcaveDensity_logConcave n _ (gaussianPositionRestrictedDensity_nonneg n K)
    (gaussianPositionRestrictedDensity_strong_logConcave n K hK)

end AffineFKProof
