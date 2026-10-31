module

public import AffineFK.GaussianKLCalculus
public import AffineFK.IsotropicCoordinates
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Actual Gaussian smoothing coordinate moments

Input coordinate L2 is derived from the literal unit second moments.
Every joint product below is L1 by L2 Holder before product integration.
Gaussian mean and covariance are Mathlib's actual standard Gaussian
theorems, not output-isotropy premises.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

theorem gaussianSmoothingIsotropy_gaussian_mean (n : ℕ) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
  simpa only [coordinateFunctional_apply] using integral_strongDual_stdGaussian (coordinateFunctional n i)

theorem gaussianSmoothingIsotropy_gaussian_second (n : ℕ) (i j : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * x j)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      if i = j then (1 : ℝ) else 0 := by
  have hG : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := IsGaussian.memLp_id _ 2 (by norm_num)
  refine ⟨(hG.eval_piLp i).integrable_mul (hG.eval_piLp j), ?_⟩
  have h := covarianceBilin_apply hG (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)
  rw [covarianceBilin_stdGaussian] at h
  change ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ j⟫ =
    ∫ z, ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      z - ∫ x, id x ∂stdGaussian (EuclideanSpace ℝ (Fin n))⟫ *
      ⟪EuclideanSpace.basisFun (Fin n) ℝ j,
        z - ∫ x, id x ∂stdGaussian (EuclideanSpace ℝ (Fin n))⟫
      ∂stdGaussian (EuclideanSpace ℝ (Fin n)) at h
  simp only [id_eq, integral_id_stdGaussian, sub_zero, EuclideanSpace.basisFun_inner] at h
  simpa [EuclideanSpace.basisFun_apply, Pi.single_apply, eq_comm] using h.symm

theorem gaussianSmoothing_product_coordinate_memLp (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (a b : ℝ) (i : Fin n) :
    MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a • p.1 + b • p.2) i) 2 (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  have hU := (isotropic_coordinate_memLp n ν hsecond i).comp_fst
    (stdGaussian (EuclideanSpace ℝ (Fin n)))
  have hG := ((IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin n))) 2
    (by norm_num)).eval_piLp i).comp_snd ν
  apply ((hU.const_mul a).add (hG.const_mul b)).ae_eq
  exact Filter.Eventually.of_forall fun p => by
    simp only [Pi.add_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, id_eq]

theorem gaussianSmoothing_product_coordinate_mean (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (a b : ℝ) (i : Fin n) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a • p.1 + b • p.2) i) (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), (a • p.1 + b • p.2) i
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) = 0 := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hU := (isotropic_coordinate_memLp n ν hsecond i).comp_fst γ
  have hG := ((IsGaussian.memLp_id γ 2 (by norm_num)).eval_piLp i).comp_snd ν
  refine ⟨(gaussianSmoothing_product_coordinate_memLp n ν hsecond a b i).integrable (by norm_num), ?_⟩
  have heq : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a • p.1 + b • p.2) i) = fun p => a * p.1 i + b * p.2 i := by
    funext p
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [heq, integral_add (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a * p.1 i)
    (g := fun p => b * p.2 i)
    ((hU.integrable (by norm_num)).const_mul a) ((hG.integrable (by norm_num)).const_mul b),
    integral_const_mul, integral_const_mul]
  have hfst : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), p.1 i ∂ν.prod γ) = 0 := by
    simpa only [hmean, probReal_univ, one_smul] using
      (integral_fun_fst (μ := ν) (ν := γ) (fun x : EuclideanSpace ℝ (Fin n) => x i))
  have hsnd : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), p.2 i ∂ν.prod γ) = 0 := by
    simpa only [γ, gaussianSmoothingIsotropy_gaussian_mean, probReal_univ, one_smul] using
      (integral_fun_snd (μ := ν) (ν := γ) (fun x : EuclideanSpace ℝ (Fin n) => x i))
  rw [hfst, hsnd, mul_zero, mul_zero, add_zero]

theorem gaussianSmoothing_product_coordinate_second (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (a b : ℝ) (i j : Fin n) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a • p.1 + b • p.2) i * (a • p.1 + b • p.2) j)
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      (a • p.1 + b • p.2) i * (a • p.1 + b • p.2) j
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
          (a ^ 2 + b ^ 2) * (if i = j then (1 : ℝ) else 0) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hUi := (isotropic_coordinate_memLp n ν hsecond i).comp_fst γ
  have hUj := (isotropic_coordinate_memLp n ν hsecond j).comp_fst γ
  have hGi := ((IsGaussian.memLp_id γ 2 (by norm_num)).eval_piLp i).comp_snd ν
  have hGj := ((IsGaussian.memLp_id γ 2 (by norm_num)).eval_piLp j).comp_snd ν
  have hUU : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 i * p.1 j)
      (ν.prod γ) := hUi.integrable_mul hUj
  have hUG : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 i * p.2 j)
      (ν.prod γ) := hUi.integrable_mul hGj
  have hGU : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 j * p.2 i)
      (ν.prod γ) := hUj.integrable_mul hGi
  have hGG : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2 i * p.2 j)
      (ν.prod γ) := hGi.integrable_mul hGj
  refine ⟨(gaussianSmoothing_product_coordinate_memLp n ν hsecond a b i).integrable_mul
    (gaussianSmoothing_product_coordinate_memLp n ν hsecond a b j), ?_⟩
  have heq : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a • p.1 + b • p.2) i * (a • p.1 + b • p.2) j) =
      fun p => ((a ^ 2 * (p.1 i * p.1 j) + (a * b) * (p.1 i * p.2 j)) +
        (a * b) * (p.1 j * p.2 i)) + b ^ 2 * (p.2 i * p.2 j) := by
    funext p
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [heq, integral_add
    (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (a ^ 2 * (p.1 i * p.1 j) + (a * b) * (p.1 i * p.2 j)) + (a * b) * (p.1 j * p.2 i))
    (g := fun p => b ^ 2 * (p.2 i * p.2 j))
    (((hUU.const_mul _).add (hUG.const_mul _)).add (hGU.const_mul _)) (hGG.const_mul _),
    integral_add (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      a ^ 2 * (p.1 i * p.1 j) + (a * b) * (p.1 i * p.2 j))
      (g := fun p => (a * b) * (p.1 j * p.2 i))
      ((hUU.const_mul _).add (hUG.const_mul _)) (hGU.const_mul _),
    integral_add (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a ^ 2 * (p.1 i * p.1 j))
      (g := fun p => (a * b) * (p.1 i * p.2 j)) (hUU.const_mul _) (hUG.const_mul _)]
  simp_rw [integral_const_mul]
  have hfst : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), p.1 i * p.1 j ∂ν.prod γ) =
      if i = j then (1 : ℝ) else 0 := by
    simpa only [hsecond, probReal_univ, one_smul] using
      (integral_fun_fst (μ := ν) (ν := γ) (fun x : EuclideanSpace ℝ (Fin n) => x i * x j))
  have hsnd : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), p.2 i * p.2 j ∂ν.prod γ) =
      if i = j then (1 : ℝ) else 0 := by
    simpa only [γ, (gaussianSmoothingIsotropy_gaussian_second n i j).2, probReal_univ, one_smul] using
      (integral_fun_snd (μ := ν) (ν := γ) (fun x : EuclideanSpace ℝ (Fin n) => x i * x j))
  have hcross (k l : Fin n) : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      p.1 k * p.2 l ∂ν.prod γ) = 0 := by
    rw [integral_prod_mul (μ := ν) (ν := γ)
      (fun x : EuclideanSpace ℝ (Fin n) => x k) (fun x : EuclideanSpace ℝ (Fin n) => x l)]
    simp only [hmean, zero_mul]
  rw [hfst, hsnd, hcross, hcross]
  ring

end AffineFKProof
