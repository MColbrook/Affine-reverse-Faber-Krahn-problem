module

public import AffineFK.VectorTestUniqueness
public import AffineFK.GaussianSmoothingProduct

/-!
# First-order weak Stein identities under Gaussian smoothing

Actual one-coordinate vector tests recover the scalar source identity.
Affine compact tests and genuine joint L1 bounds permit Fubini, after
which Gaussian integration by parts gives the exact first-order factor a.
The source field is only assumed L2; no derivative of that field is used.

The compact-test and product integration lemmas are reused from the earlier
project development, with their Mathlib attribution retained there.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem firstOrder_source_component_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪s x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => s x i * φ x) ν ∧
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * φ x) ν ∧
    Integrable (partialTest n i φ) ν ∧
    (∫ x, s x i * φ x ∂ν) = (∫ x, x i * φ x ∂ν) - ∫ x, partialTest n i φ x ∂ν := by
  have hφ := testFunction_memLp_two n ν φ
  have hscore : Integrable (fun x => s x i * φ x) ν := (hs.eval_piLp i).integrable_mul hφ
  have hfirst : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * φ x) ν :=
    (hxi i).integrable_mul hφ
  have hderiv : Integrable (partialTest n i φ) ν :=
    (testFunction_memLp_two n ν (partialTest n i φ)).integrable (by norm_num)
  refine ⟨hscore, hfirst, hderiv, ?_⟩
  have h := hweak (singleComponentTest n i φ)
  simp_rw [singleComponentTest_inner_at, vectorDivergence_singleComponentTest] at h
  rw [integral_sub hfirst hderiv] at h
  exact h

theorem firstOrder_product_component_identity
    (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, s x i * ψ x ∂ν) = (∫ x, x i * ψ x ∂ν) - ∫ x, partialTest n i ψ x ∂ν)
    (a : ℝ) (ha : a ≠ 0) (b : ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      s p.1 i * φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      p.1 i * φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    (∫ p, s p.1 i * φ (a • p.1 + b • p.2) ∂ν.prod η) =
      (∫ p, p.1 i * φ (a • p.1 + b • p.2) ∂ν.prod η) -
        a * (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod η) := by
  let Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hΦ : Continuous Φ := by fun_prop
  have hscore := integrable_fst_mul_test_comp n ν η (fun x => s x i)
    ((hs.eval_piLp i).integrable (by norm_num)) Φ hΦ φ
  have hfirst := integrable_fst_mul_test_comp n ν η (fun x => x i)
    (hxi.integrable (by norm_num)) Φ hΦ φ
  have hderiv : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2)) (ν.prod η) := by
    simpa only [one_mul] using integrable_fst_mul_test_comp n ν η (fun _ => (1 : ℝ))
      (integrable_const 1) Φ hΦ (partialTest n i φ)
  have hfixed (y : EuclideanSpace ℝ (Fin n)) :
      (∫ x, s x i * φ (a • x + b • y) ∂ν) =
        (∫ x, x i * φ (a • x + b • y) ∂ν) -
          a * (∫ x, partialTest n i φ (a • x + b • y) ∂ν) := by
    have h := hidentity (gaussianAffineTest n a ha (b • y) φ)
    have hdpoint (x : EuclideanSpace ℝ (Fin n)) :
        partialTest n i (gaussianAffineTest n a ha (b • y) φ) x =
          a * partialTest n i φ (a • x + b • y) := by
      rw [partialTest_gaussianAffineTest]
      change a * gaussianAffineTest n a ha (b • y) (partialTest n i φ) x = _
      rw [gaussianAffineTest_apply]
    have hd : (∫ x, partialTest n i (gaussianAffineTest n a ha (b • y) φ) x ∂ν) =
        a * (∫ x, partialTest n i φ (a • x + b • y) ∂ν) := by
      calc
        _ = ∫ x, a * partialTest n i φ (a • x + b • y) ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall hdpoint)
        _ = _ := integral_const_mul _ _
    rw [hd] at h
    simpa only [gaussianAffineTest_apply] using h
  refine ⟨hscore, hfirst, hderiv, ?_⟩
  calc
    _ = ∫ y, (∫ x, s x i * φ (a • x + b • y) ∂ν) ∂η := integral_prod_symm _ hscore
    _ = ∫ y, ((∫ x, x i * φ (a • x + b • y) ∂ν) -
        a * (∫ x, partialTest n i φ (a • x + b • y) ∂ν)) ∂η :=
      integral_congr_ae (Filter.Eventually.of_forall hfixed)
    _ = _ := by
      rw [integral_sub hfirst.integral_prod_right (hderiv.integral_prod_right.const_mul a),
        integral_const_mul, ← integral_prod_symm _ hfirst, ← integral_prod_symm _ hderiv]

theorem firstOrder_smoothed_component_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, s x i * ψ x ∂ν) = (∫ x, x i * ψ x ∂ν) - ∫ x, partialTest n i ψ x ∂ν)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a • p.1 + b • p.2) i * φ (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      s p.1 i * φ (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p, (a • p.1 + b • p.2) i * φ (a • p.1 + b • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) -
      (∫ p, partialTest n i φ (a • p.1 + b • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      a * (∫ p, s p.1 i * φ (a • p.1 + b • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hS := firstOrder_product_component_identity n ν γ s hs i hxi hidentity a ha b φ
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
    exact (hS.2.1.const_mul a).add (hG.1.const_mul b)
  have hfirstIntegral :
      (∫ p, (a • p.1 + b • p.2) i * φ (a • p.1 + b • p.2) ∂ν.prod γ) =
        a * (∫ p, p.1 i * φ (a • p.1 + b • p.2) ∂ν.prod γ) +
          b * (∫ p, p.2 i * φ (a • p.1 + b • p.2) ∂ν.prod γ) := by
    rw [hfun, integral_add (hS.2.1.const_mul a) (hG.1.const_mul b),
      integral_const_mul, integral_const_mul]
  have hbb : b * b = 1 - a * a := by nlinarith [hab]
  refine ⟨hfirst, hS.2.2.1, hS.1, ?_⟩
  calc
    _ = a * (∫ p, p.1 i * φ (a • p.1 + b • p.2) ∂ν.prod γ) +
        b * (b * (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod γ)) -
        (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod γ) := by
      rw [hfirstIntegral, hG.2.2]
    _ = a * ((∫ p, p.1 i * φ (a • p.1 + b • p.2) ∂ν.prod γ) -
        a * (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod γ)) := by
      rw [← mul_assoc b b, hbb]
      ring
    _ = _ := by rw [← hS.2.2.2]

end AffineFKProof
