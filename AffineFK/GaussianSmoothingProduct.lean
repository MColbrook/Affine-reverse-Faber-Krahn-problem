module

public import AffineFK.AffineGaussianIntegrationByParts
public import AffineFK.AffineProductIntegrability
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian integration by parts averaged over the other input

The independent product law is explicit. Bounded smooth tests and the
Gaussian first moment prove joint integrability before Fubini. The
coefficient b is the genuine chain-rule factor in the Gaussian variable.
Gaussian moments reuse Mathlib's Fernique theorem and its contributors.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

theorem product_gaussian_smoothing_integration_by_parts
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (a b : ℝ) (hb : b ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      p.2 i * φ (a • p.1 + b • p.2)) (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2)) (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p, p.2 i * φ (a • p.1 + b • p.2) ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      b * (∫ p, partialTest n i φ (a • p.1 + b • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hΦ : Continuous Φ := by fun_prop
  have hGi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 γ :=
    (IsGaussian.memLp_id γ 2 (by norm_num)).eval_piLp i
  have hfirst := integrable_snd_mul_test_comp n ν γ (fun x => x i)
    (hGi.integrable (by norm_num)) Φ hΦ φ
  have hderiv : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2)) (ν.prod γ) := by
    simpa only [one_mul] using integrable_fst_mul_test_comp n ν γ (fun _ => (1 : ℝ))
      (integrable_const 1) Φ hΦ (partialTest n i φ)
  refine ⟨hfirst, hderiv, ?_⟩
  calc
    _ = ∫ u, (∫ g, g i * φ (a • u + b • g) ∂γ) ∂ν := integral_prod _ hfirst
    _ = ∫ u, b * (∫ g, partialTest n i φ (a • u + b • g) ∂γ) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        simpa only [add_comm] using
          (stdGaussian_affine_integration_by_parts n i b hb (a • u) φ).2.2
    _ = b * (∫ u, (∫ g, partialTest n i φ (a • u + b • g) ∂γ) ∂ν) := integral_const_mul _ _
    _ = _ := by rw [← integral_prod _ hderiv]

end AffineFKProof
