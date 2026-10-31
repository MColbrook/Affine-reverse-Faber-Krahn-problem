module

public import AffineFK.AffineGaussianIntegrationByParts
public import AffineFK.AffineProductIntegrability

/-!
# Tensor-weighted Gaussian second integration by parts

The coefficient depends only on the first independent input. Its L1
membership and the genuine Gaussian quadratic moment give joint L1
membership of the polynomial-times-test integrand before Fubini. The
Gaussian chain-rule factor is b², with no derivatives of the tensor.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

theorem product_gaussian_weighted_second_integration_by_parts
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i j k : Fin n) (a b : ℝ) (hb : b ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (T p.1 (i, j, k) * (p.2 j * p.2 k - if j = k then 1 else 0)) * φ (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p, (T p.1 (i, j, k) * (p.2 j * p.2 k - if j = k then 1 else 0)) * φ (a • p.1 + b • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      b ^ 2 * (∫ p, T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hΦ : Continuous Φ := by fun_prop
  have hTc : Integrable (fun u => T u (i, j, k)) ν := (hT.eval_piLp (i, j, k)).integrable (by norm_num)
  have hleft := integrable_fst_mul_test_comp n ν γ (fun u => T u (i, j, k)) hTc
    Φ hΦ (partialTest n k (partialTest n j φ))
  have hright := integrable_product_mul_test_comp n ν γ (fun u => T u (i, j, k))
    (fun g => g j * g k - if j = k then 1 else 0) hTc
    ((stdGaussian_quadratic_memLp n j k).integrable (by norm_num)) Φ hΦ φ
  have hfixed (u : EuclideanSpace ℝ (Fin n)) :
      (∫ g, (T u (i, j, k) * (g j * g k - if j = k then 1 else 0)) * φ (a • u + b • g) ∂γ) =
        b ^ 2 * (∫ g, T u (i, j, k) * partialTest n k (partialTest n j φ) (a • u + b • g) ∂γ) := by
    have hgauss : (∫ g, (g j * g k - if j = k then 1 else 0) * φ (a • u + b • g) ∂γ) =
        b ^ 2 * (∫ g, partialTest n k (partialTest n j φ) (a • u + b • g) ∂γ) := by
      simpa only [add_comm] using (stdGaussian_affine_second_integration_by_parts n j k b hb (a • u) φ).2.2
    calc
      _ = T u (i, j, k) * (∫ g, (g j * g k - if j = k then 1 else 0) * φ (a • u + b • g) ∂γ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun g => by
          change (T u (i, j, k) * (g j * g k - if j = k then 1 else 0)) * φ (a • u + b • g) =
            T u (i, j, k) * ((g j * g k - if j = k then 1 else 0) * φ (a • u + b • g))
          ring
      _ = _ := by rw [hgauss, integral_const_mul]; ring
  refine ⟨hleft, hright, ?_⟩
  calc
    _ = ∫ u, (∫ g, (T u (i, j, k) * (g j * g k - if j = k then 1 else 0)) * φ (a • u + b • g) ∂γ) ∂ν :=
      integral_prod _ hright
    _ = ∫ u, b ^ 2 * (∫ g, T u (i, j, k) * partialTest n k (partialTest n j φ) (a • u + b • g) ∂γ) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hfixed
    _ = _ := by rw [integral_const_mul, ← integral_prod _ hleft]

end AffineFKProof
