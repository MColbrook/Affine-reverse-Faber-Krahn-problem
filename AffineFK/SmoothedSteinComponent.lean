module

public import AffineFK.SmoothedSteinProduct
public import AffineFK.GaussianSmoothingProduct

/-!
# Gaussian cancellation in the smoothed Stein identity

For a²+b²=1, the Gaussian first-order term cancels the missing
derivative term. The resulting factor is exactly a³. This is an actual
compact-test identity on the independent product law; identification
with the logarithmic relative score is a separate analytic step.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

theorem smoothed_stein_component_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, x i * ψ x ∂ν) - (∫ x, partialTest n i ψ x ∂ν) =
        ∫ x, tensorPartialContraction n T i ψ x ∂ν)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a • p.1 + b • p.2) i * φ (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2)) (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p, (a • p.1 + b • p.2) i * φ (a • p.1 + b • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) -
      (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      a ^ 3 * (∫ p, ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hS := product_smoothed_stein_component_identity n ν γ T hT i hxi hidentity a ha b φ
  have hG := product_gaussian_smoothing_integration_by_parts n ν i a b hb φ
  have hcoord (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
      (a • p.1 + b • p.2) i = a * p.1 i + b * p.2 i := by
    have h := map_add (coordinateFunctional n i) (a • p.1) (b • p.2)
    simpa only [map_smul, coordinateFunctional_apply, smul_eq_mul] using h
  have hfun : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a • p.1 + b • p.2) i * φ (a • p.1 + b • p.2)) =
      (fun p => a * (p.1 i * φ (a • p.1 + b • p.2)) +
        b * (p.2 i * φ (a • p.1 + b • p.2))) := by
    funext p
    rw [hcoord]
    ring
  have hfirst : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a • p.1 + b • p.2) i * φ (a • p.1 + b • p.2)) (ν.prod γ) := by
    rw [hfun]
    exact (hS.1.const_mul a).add (hG.1.const_mul b)
  have hfirstIntegral :
      (∫ p, (a • p.1 + b • p.2) i * φ (a • p.1 + b • p.2) ∂ν.prod γ) =
        a * (∫ p, p.1 i * φ (a • p.1 + b • p.2) ∂ν.prod γ) +
          b * (∫ p, p.2 i * φ (a • p.1 + b • p.2) ∂ν.prod γ) := by
    rw [hfun, integral_add (hS.1.const_mul a) (hG.1.const_mul b), integral_const_mul, integral_const_mul]
  have hbb : b * b = 1 - a * a := by nlinarith [hab]
  refine ⟨hfirst, hS.2.1, hS.2.2.1, ?_⟩
  calc
    _ = a * (∫ p, p.1 i * φ (a • p.1 + b • p.2) ∂ν.prod γ) +
        b * (b * (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod γ)) -
        (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod γ) := by
      rw [hfirstIntegral, hG.2.2]
    _ = a * ((∫ p, p.1 i * φ (a • p.1 + b • p.2) ∂ν.prod γ) -
        a * (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod γ)) := by
      rw [← mul_assoc b b, hbb]
      ring
    _ = a * (a ^ 2 * (∫ p, ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2) ∂ν.prod γ)) := by
      rw [hS.2.2.2]
    _ = _ := by ring

end AffineFKProof
