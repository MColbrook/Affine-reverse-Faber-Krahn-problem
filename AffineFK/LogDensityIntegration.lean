module

public import AffineFK.WeightedTestIntegration
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Integration by parts for the logarithmic density gradient

The density is an actual smooth strictly positive function, and its
measure is rho times Lebesgue volume. No global L2 assumption on its
logarithmic gradient is needed for these compact-test identities.
The Frechet logarithmic chain rule and Haar integration by parts are
reused from Mathlib, with genuine integrability of each product.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff

theorem continuous_log_density_gradient
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) :
    Continuous (gradient (fun x => Real.log (ρ x))) := by
  have hlog := hρ.log (fun x => (hρpos x).ne')
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
    (hlog.continuous_fderiv (by simp))

theorem log_density_gradient_coordinate
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    gradient (fun y => Real.log (ρ y)) x j =
      (ρ x)⁻¹ * fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  calc
    _ = ⟪gradient (fun y => Real.log (ρ y)) x, EuclideanSpace.basisFun (Fin n) ℝ j⟫ := by
      rw [real_inner_comm, EuclideanSpace.basisFun_inner]
    _ = fderiv ℝ (fun y => Real.log (ρ y)) x (EuclideanSpace.basisFun (Fin n) ℝ j) := inner_gradient_left
    _ = _ := by
      rw [fderiv.log ((hρ.differentiable (by simp)).differentiableAt) (hρpos x).ne']
      rfl

theorem log_density_gradient_test_integration_by_parts
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => gradient (fun y => Real.log (ρ y)) x j * φ x) (densityMeasure n ρ) ∧
    Integrable (partialTest n j φ) (densityMeasure n ρ) ∧
    (∫ x, gradient (fun y => Real.log (ρ y)) x j * φ x ∂densityMeasure n ρ) =
      -(∫ x, partialTest n j φ x ∂densityMeasure n ρ) := by
  have hg : Continuous (fun x => gradient (fun y => Real.log (ρ y)) x j) := by
    have hc := continuous_log_density_gradient n ρ hρ hρpos
    fun_prop
  have hleft : Integrable (fun x => gradient (fun y => Real.log (ρ y)) x j * φ x) (densityMeasure n ρ) :=
    (hg.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hpartial : Integrable (partialTest n j φ) (densityMeasure n ρ) :=
    (partialTest n j φ).continuous.integrable_of_hasCompactSupport (partialTest n j φ).hasCompactSupport
  have hdρ : Continuous (fun x => fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ j)) :=
    (hρ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hL : Integrable (fun x => fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ j) * φ x) :=
    (hdρ.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hR : Integrable (fun x => ρ x * fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
    simp_rw [← partialTest_fderiv n j φ]
    exact (hρ.continuous.mul (partialTest n j φ).continuous).integrable_of_hasCompactSupport
      (partialTest n j φ).hasCompactSupport.mul_left
  have hproduct : Integrable (fun x => ρ x * φ x) :=
    (hρ.continuous.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hL hR hproduct
    (fun x _ => (hρ.differentiable (by simp)).differentiableAt)
    (fun x _ => (φ.contDiff.differentiable (by simp)).differentiableAt)
  refine ⟨hleft, hpartial, ?_⟩
  calc
    _ = ∫ x, fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ j) * φ x := by
      rw [density_integral_eq n ρ hρ.continuous (fun x => (hρpos x).le)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change ρ x * (gradient (fun y => Real.log (ρ y)) x j * φ x) = _
        rw [log_density_gradient_coordinate n ρ hρ hρpos]
        field_simp [(hρpos x).ne']
    _ = -(∫ x, ρ x * fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by linarith [hibp]
    _ = _ := by
      rw [density_integral_eq n ρ hρ.continuous (fun x => (hρpos x).le)]
      simp_rw [partialTest_fderiv n j φ]

end AffineFKProof
