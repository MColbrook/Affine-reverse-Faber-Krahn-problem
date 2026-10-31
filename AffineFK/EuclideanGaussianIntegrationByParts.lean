module

public import AffineFK.ProductGaussianIntegrationByParts
public import AffineFK.GaussianEuclideanTests
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.HasLaw

/-!
# Coordinate integration by parts for the actual Euclidean standard Gaussian

Mathlib's map_pi_eq_stdGaussian identifies the finite product of real
standard Gaussians with its actual Euclidean standard Gaussian measure.
The test transport preserves the coordinate partial derivative exactly.
Gaussian measure and change-of-law results are due to Remy Degenne and
Etienne Marion and the other Mathlib contributors credited in the sources.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

theorem stdGaussian_coordinate_integration_by_parts (n : ℕ) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x j * φ x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (partialTest n j φ) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, x j * φ x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ∫ x, partialTest n j φ x ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  have hleft : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x j * φ x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    have hm : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x j * φ x) := by fun_prop
    exact hm.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hright : Integrable (partialTest n j φ) (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    (partialTest n j φ).continuous.integrable_of_hasCompactSupport (partialTest n j φ).hasCompactSupport
  have hlaw : HasLaw (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (Measure.pi fun _ => gaussianReal 0 1) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  refine ⟨hleft, hright, ?_⟩
  calc
    _ = ∫ x : Fin n → ℝ, x j * euclideanToPiTest n φ x
        ∂Measure.pi (fun _ => gaussianReal 0 1) :=
      (hlaw.integral_comp hleft.aestronglyMeasurable).symm
    _ = ∫ x : Fin n → ℝ, piPartialTest n j (euclideanToPiTest n φ) x
        ∂Measure.pi (fun _ => gaussianReal 0 1) :=
      (productGaussian_integration_by_parts n j (euclideanToPiTest n φ)).2.2
    _ = ∫ x : Fin n → ℝ, partialTest n j φ (WithLp.toLp 2 x)
        ∂Measure.pi (fun _ => gaussianReal 0 1) := by
      simp_rw [piPartialTest_euclideanToPiTest]
    _ = _ := hlaw.integral_comp hright.aestronglyMeasurable

end AffineFKProof
