module

public import AffineFK.GaussianVarianceCorrelation

/-! Guarded two-input Gaussian integration by parts for covariance interpolation. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace

def gaussianVarianceMixedTest (n : ℕ)
    (f ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  ⟨fun x => f x * ψ (a • x + z),
    f.contDiff.mul (ψ.contDiff.comp (by fun_prop)),
    f.hasCompactSupport.mul_right, Set.subset_univ _⟩

theorem gaussianVarianceMixedTest_partial (n : ℕ) (i : Fin n)
    (f ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (a : ℝ) (z x : EuclideanSpace ℝ (Fin n)) :
    partialTest n i (gaussianVarianceMixedTest n f ψ a z) x =
      partialTest n i f x * ψ (a • x + z) + a * (f x * partialTest n i ψ (a • x + z)) := by
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    a • ContinuousLinearMap.id ℝ _
  have hA : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => a • y + z) A x :=
    A.hasFDerivAt.add_const z
  have hψ := ((ψ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x hA
  have hm := ((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).mul hψ
  rw [partialTest_fderiv]
  change fderiv ℝ ((f : EuclideanSpace ℝ (Fin n) → ℝ) *
    ((ψ : EuclideanSpace ℝ (Fin n) → ℝ) ∘ fun y => a • y + z)) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) = _
  rw [hm.fderiv]
  simp only [add_apply, smul_apply, Function.comp_apply,
    ContinuousLinearMap.comp_apply, A, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul, ← partialTest_fderiv]
  ring

theorem gaussianVariance_IBP_fst (n : ℕ) (i : Fin n)
    (f ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (a b : ℝ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (p.1 i * f p.1) * ψ (a • p.1 + b • p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i f p.1 * ψ (a • p.1 + b • p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      f p.1 * partialTest n i ψ (a • p.1 + b • p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      (p.1 i * f p.1) * ψ (a • p.1 + b • p.2)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      (∫ p, partialTest n i f p.1 * ψ (a • p.1 + b • p.2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) +
      a * (∫ p, f p.1 * partialTest n i ψ (a • p.1 + b • p.2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hΦ : Continuous Φ := by fun_prop
  have hxf : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * f x) γ :=
    (show Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i * f x) from by fun_prop).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_left
  have hf : Integrable (f : EuclideanSpace ℝ (Fin n) → ℝ) γ :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hd : Integrable (partialTest n i f) γ :=
    (partialTest n i f).continuous.integrable_of_hasCompactSupport (partialTest n i f).hasCompactSupport
  have hL := integrable_fst_mul_test_comp n γ γ _ hxf Φ hΦ ψ
  have hR := integrable_fst_mul_test_comp n γ γ _ hd Φ hΦ ψ
  have hS := integrable_fst_mul_test_comp n γ γ _ hf Φ hΦ (partialTest n i ψ)
  have htotal := hR.add (hS.const_mul a)
  have hfixed (y : EuclideanSpace ℝ (Fin n)) :
      (∫ x, (x i * f x) * ψ (a • x + b • y) ∂γ) =
      ∫ x, partialTest n i f x * ψ (a • x + b • y) + a * (f x * partialTest n i ψ (a • x + b • y)) ∂γ := by
    have h := (stdGaussian_coordinate_integration_by_parts n i
      (gaussianVarianceMixedTest n f ψ a (b • y))).2.2
    calc
      _ = ∫ x, x i * gaussianVarianceMixedTest n f ψ a (b • y) x ∂γ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by change (x i * f x) * _ = x i * (f x * _); ring
      _ = ∫ x, partialTest n i (gaussianVarianceMixedTest n f ψ a (b • y)) x ∂γ := h
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => gaussianVarianceMixedTest_partial n i f ψ a (b • y) x)
  refine ⟨hL, hR, hS, ?_⟩
  calc
    _ = ∫ y, ∫ x, (x i * f x) * ψ (a • x + b • y) ∂γ ∂γ := integral_prod_symm _ hL
    _ = ∫ y, ∫ x, partialTest n i f x * ψ (a • x + b • y) +
        a * (f x * partialTest n i ψ (a • x + b • y)) ∂γ ∂γ :=
      integral_congr_ae (Eventually.of_forall hfixed)
    _ = ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i f p.1 * ψ (Φ p) + a * (f p.1 * partialTest n i ψ (Φ p)) ∂γ.prod γ :=
      (integral_prod_symm _ htotal).symm
    _ = _ := by rw [integral_add hR (hS.const_mul a), integral_const_mul]

theorem gaussianVariance_IBP_snd (n : ℕ) (i : Fin n)
    (f ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (a b : ℝ) (hb : b ≠ 0) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (f p.1 * p.2 i) * ψ (a • p.1 + b • p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      f p.1 * partialTest n i ψ (a • p.1 + b • p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      (f p.1 * p.2 i) * ψ (a • p.1 + b • p.2)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      b * (∫ p, f p.1 * partialTest n i ψ (a • p.1 + b • p.2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hΦ : Continuous Φ := by fun_prop
  have hf : Integrable (f : EuclideanSpace ℝ (Fin n) → ℝ) γ :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hYi : Integrable (fun y : EuclideanSpace ℝ (Fin n) => y i) γ :=
    ((IsGaussian.memLp_id γ 2 (by norm_num)).eval_piLp i).integrable (by norm_num)
  have hL := integrable_product_mul_test_comp n γ γ _ _ hf hYi Φ hΦ ψ
  have hR := integrable_fst_mul_test_comp n γ γ _ hf Φ hΦ (partialTest n i ψ)
  have hfixed (x : EuclideanSpace ℝ (Fin n)) :
      (∫ y, (f x * y i) * ψ (a • x + b • y) ∂γ) =
        b * (∫ y, f x * partialTest n i ψ (a • x + b • y) ∂γ) := by
    have hG : (∫ y, y i * ψ (a • x + b • y) ∂γ) =
        b * (∫ y, partialTest n i ψ (a • x + b • y) ∂γ) := by
      simpa only [add_comm] using (stdGaussian_affine_integration_by_parts n i b hb (a • x) ψ).2.2
    calc
      _ = f x * (∫ y, y i * ψ (a • x + b • y) ∂γ) := by
        simp_rw [mul_assoc]
        rw [integral_const_mul]
      _ = f x * (b * (∫ y, partialTest n i ψ (a • x + b • y) ∂γ)) := by rw [hG]
      _ = _ := by rw [integral_const_mul]; ring
  refine ⟨hL, hR, ?_⟩
  calc
    _ = ∫ x, ∫ y, (f x * y i) * ψ (a • x + b • y) ∂γ ∂γ := integral_prod _ hL
    _ = ∫ x, b * (∫ y, f x * partialTest n i ψ (a • x + b • y) ∂γ) ∂γ :=
      integral_congr_ae (Eventually.of_forall hfixed)
    _ = _ := by rw [integral_const_mul, ← integral_prod _ hR]

end AffineFKProof
