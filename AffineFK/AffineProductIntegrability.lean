module

public import AffineFK.ProductSteinIdentity
public import AffineFK.EuclideanGaussianCovariance

/-!
# Integrability for product-space affine tests

A bounded compact smooth test may be composed with any continuous map of
the two variables. Integrable coefficients in either variable, or a
product of two integrable coefficients, then give genuine joint L1
membership before Fubini is applied. This extends the bounded-test
argument already used in ProductSteinIdentity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

theorem integrable_fst_mul_test_comp (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w ν)
    (Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : Continuous Φ) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p => w p.1 * φ (Φ p)) (ν.prod η) := by
  let f := TestFunction.toBoundedContinuousFunctionCLM ℝ φ
  apply (hw.comp_fst η).mul_bdd (φ.continuous.comp hΦ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => f.norm_coe_le_norm (Φ p)

theorem integrable_snd_mul_test_comp (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w η)
    (Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : Continuous Φ) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p => w p.2 * φ (Φ p)) (ν.prod η) := by
  let f := TestFunction.toBoundedContinuousFunctionCLM ℝ φ
  apply (hw.comp_snd ν).mul_bdd (φ.continuous.comp hΦ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => f.norm_coe_le_norm (Φ p)

theorem integrable_product_mul_test_comp (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (v w : EuclideanSpace ℝ (Fin n) → ℝ) (hv : Integrable v ν) (hw : Integrable w η)
    (Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : Continuous Φ) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p => (v p.1 * w p.2) * φ (Φ p)) (ν.prod η) := by
  let f := TestFunction.toBoundedContinuousFunctionCLM ℝ φ
  apply (hv.mul_prod hw).mul_bdd (φ.continuous.comp hΦ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => f.norm_coe_le_norm (Φ p)

theorem stdGaussian_quadratic_memLp (n : ℕ) (j k : Fin n) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x j * x k - if j = k then 1 else 0) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x j * x k - if j = k then 1 else 0) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  convert (stdGaussian_quadratic_pair_covariance n j k j k).1 using 1
  funext x
  rw [Real.norm_eq_abs, sq_abs, pow_two]

end AffineFKProof
