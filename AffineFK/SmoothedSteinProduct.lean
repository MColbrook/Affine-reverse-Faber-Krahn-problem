module

public import AffineFK.AffineProductIntegrability

/-!
# The second-order Stein identity under affine smoothing

An arbitrary independent second input may be averaged against the
genuine compact-test Stein identity in the first variable. All three
joint integrands are in L1 before Fubini. The derivative factors are
exactly a and a². Gaussian cancellation is a subsequent step.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions

theorem product_smoothed_stein_component_identity
    (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, x i * ψ x ∂ν) - (∫ x, partialTest n i ψ x ∂ν) =
        ∫ x, tensorPartialContraction n T i ψ x ∂ν)
    (a : ℝ) (ha : a ≠ 0) (b : ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      p.1 i * φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2)) (ν.prod η) ∧
    (∫ p, p.1 i * φ (a • p.1 + b • p.2) ∂ν.prod η) -
      a * (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod η) =
      a ^ 2 * (∫ p, ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2) ∂ν.prod η) := by
  let Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hΦ : Continuous Φ := by fun_prop
  have hfirst := integrable_fst_mul_test_comp n ν η (fun x => x i)
    (hxi.integrable (by norm_num)) Φ hΦ φ
  have hderiv : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2)) (ν.prod η) := by
    simpa only [one_mul] using integrable_fst_mul_test_comp n ν η (fun _ => (1 : ℝ))
      (integrable_const 1) Φ hΦ (partialTest n i φ)
  have hright : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2)) (ν.prod η) := by
    apply integrable_finsetSum Finset.univ
    intro j _
    apply integrable_finsetSum Finset.univ
    intro k _
    exact integrable_fst_mul_test_comp n ν η (fun x => T x (i, j, k))
      ((hT.eval_piLp (i, j, k)).integrable (by norm_num)) Φ hΦ (partialTest n k (partialTest n j φ))
  have harg (x y : EuclideanSpace ℝ (Fin n)) :
      a • (x + a⁻¹ • (b • y)) = a • x + b • y := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ha, one_smul]
  have hfixed (y : EuclideanSpace ℝ (Fin n)) :
      (∫ x, x i * φ (a • x + b • y) ∂ν) -
        a * (∫ x, partialTest n i φ (a • x + b • y) ∂ν) =
        a ^ 2 * (∫ x, ∑ j : Fin n, ∑ k : Fin n,
          T x (i, j, k) * partialTest n k (partialTest n j φ) (a • x + b • y) ∂ν) := by
    simpa only [inv_inv, harg, pow_two] using
      (affine_stein_component_identity n ν T hT i hxi hidentity a⁻¹ (inv_ne_zero ha)
        (a⁻¹ • (b • y)) φ).2.2.2
  refine ⟨hfirst, hderiv, hright, ?_⟩
  calc
    _ = (∫ y, (∫ x, x i * φ (a • x + b • y) ∂ν) ∂η) -
        a * (∫ y, (∫ x, partialTest n i φ (a • x + b • y) ∂ν) ∂η) := by
      rw [integral_prod_symm _ hfirst, integral_prod_symm _ hderiv]
    _ = ∫ y, ((∫ x, x i * φ (a • x + b • y) ∂ν) -
        a * (∫ x, partialTest n i φ (a • x + b • y) ∂ν)) ∂η := by
      rw [integral_sub hfirst.integral_prod_right (hderiv.integral_prod_right.const_mul a),
        integral_const_mul]
    _ = ∫ y, a ^ 2 * (∫ x, ∑ j : Fin n, ∑ k : Fin n,
        T x (i, j, k) * partialTest n k (partialTest n j φ) (a • x + b • y) ∂ν) ∂η := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hfixed
    _ = _ := by rw [integral_const_mul, ← integral_prod_symm _ hright]

end AffineFKProof
