module

public import AffineFK.AffineSteinIdentity
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating the affine Stein identity over the other input

Compact smooth tests and all their partial derivatives are uniformly bounded.
This gives joint integrability against the product law even though the affine
sum has noncompact fibres. Fubini is applied only after those joint bounds
have been supplied. The translation law may be any probability measure.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem integrable_fst_mul_affine_test
    (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure η]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Integrable w ν)
    (r : ℝ) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      w p.1 * φ (r⁻¹ • (p.1 + p.2 + b))) (ν.prod η) := by
  let f := TestFunction.toBoundedContinuousFunctionCLM ℝ φ
  have hmap : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      r⁻¹ • (p.1 + p.2 + b)) := by fun_prop
  have hm : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        φ (r⁻¹ • (p.1 + p.2 + b))) (ν.prod η) :=
    (φ.continuous.comp hmap).aestronglyMeasurable
  apply (hw.comp_fst η).mul_bdd hm
  exact Filter.Eventually.of_forall fun p => f.norm_coe_le_norm (r⁻¹ • (p.1 + p.2 + b))

theorem product_affine_tensor_contraction_integrable
    (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n) (r : ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (p.1 + p.2))) (ν.prod η) := by
  apply integrable_finsetSum Finset.univ
  intro j _hj
  apply integrable_finsetSum Finset.univ
  intro k _hk
  have h := integrable_fst_mul_affine_test n ν η (fun x => T x (i, j, k))
    ((hT.eval_piLp (i, j, k)).integrable (by norm_num)) r 0 (partialTest n k (partialTest n j φ))
  simpa only [add_zero] using h

theorem product_affine_stein_component_identity
    (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, x i * ψ x ∂ν) - (∫ x, partialTest n i ψ x ∂ν) =
        ∫ x, tensorPartialContraction n T i ψ x ∂ν)
    (r : ℝ) (hr : r ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      p.1 i * φ (r⁻¹ • (p.1 + p.2))) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (r⁻¹ • (p.1 + p.2))) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (p.1 + p.2))) (ν.prod η) ∧
    (∫ p, p.1 i * φ (r⁻¹ • (p.1 + p.2)) ∂ν.prod η) -
      r⁻¹ * (∫ p, partialTest n i φ (r⁻¹ • (p.1 + p.2)) ∂ν.prod η) =
      (r⁻¹ * r⁻¹) * (∫ p, ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (p.1 + p.2)) ∂ν.prod η) := by
  have hfirst : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      p.1 i * φ (r⁻¹ • (p.1 + p.2))) (ν.prod η) := by
    simpa only [add_zero] using integrable_fst_mul_affine_test n ν η
      (fun x => x i) (hxi.integrable (by norm_num)) r 0 φ
  have hderiv : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (r⁻¹ • (p.1 + p.2))) (ν.prod η) := by
    have h := integrable_fst_mul_affine_test n ν η (fun _ => (1 : ℝ))
      (integrable_const 1) r 0 (partialTest n i φ)
    simpa only [one_mul, add_zero] using h
  have hright := product_affine_tensor_contraction_integrable n ν η T hT i r φ
  refine ⟨hfirst, hderiv, hright, ?_⟩
  calc
    _ = (∫ y, (∫ x, x i * φ (r⁻¹ • (x + y)) ∂ν) ∂η) -
        r⁻¹ * (∫ y, (∫ x, partialTest n i φ (r⁻¹ • (x + y)) ∂ν) ∂η) := by
      rw [integral_prod_symm _ hfirst, integral_prod_symm _ hderiv]
    _ = ∫ y, ((∫ x, x i * φ (r⁻¹ • (x + y)) ∂ν) -
        r⁻¹ * (∫ x, partialTest n i φ (r⁻¹ • (x + y)) ∂ν)) ∂η := by
      rw [integral_sub hfirst.integral_prod_right (hderiv.integral_prod_right.const_mul r⁻¹),
        integral_const_mul]
    _ = ∫ y, (r⁻¹ * r⁻¹) * (∫ x, ∑ j : Fin n, ∑ k : Fin n,
        T x (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (x + y)) ∂ν) ∂η := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y =>
        (affine_stein_component_identity n ν T hT i hxi hidentity r hr y φ).2.2.2
    _ = _ := by
      rw [integral_const_mul, ← integral_prod_symm _ hright]

end AffineFKProof
