module

public import AffineFK.OUConvolutionInformationCalculus
public import AffineFK.OUConvolutionHessian
public import AffineFK.NormalizedConvolutionIsotropy

/-!
# Actual OU Hessian regression deficit

The two one-sided Poincare estimates concern the genuine relative scores
and actual derivative matrices. Their sum controls the product Hessian
difference, and the proved convolution Hessian deficit then gives
Bizeul's Lemma 8 at positive time, with actual numerical relative Fisher
information. No scalar dissipation or jump inequality is a premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal Matrix.Norms.L2Operator

theorem matrixHilbertSchmidtSq_sub_comm (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixHilbertSchmidtSq (A - B) = matrixHilbertSchmidtSq (B - A) := by
  have heq : A - B = -(B - A) := by abel
  rw [heq, matrixHilbertSchmidtSq_neg]

theorem ou_relativeScore_pair_regression (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (hmeanν : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hmeanη : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂η) = 0)
    (hcovν : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) =
      if i = j then (1 : ℝ) else 0)
    (hcovη : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂η) =
      if i = j then (1 : ℝ) else 0)
    (P : ℝ≥0) (hPone : 1 ≤ P)
    (hPν : poincareConstant n ν ≤ (P : ℝ≥0∞)) (hPη : poincareConstant n η ≤ (P : ℝ≥0∞))
    (t : ℝ) (ht : 0 < t) :
    let ρ : Measure (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) → ℝ :=
      fun κ => gaussianSmoothingDensity n κ (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    let I : Measure (EuclideanSpace ℝ (Fin n)) → ℝ := fun κ => (relativeFisherMeasure n (ouInitialLaw n κ t)).toReal
    let K : Measure (EuclideanSpace ℝ (Fin n)) → ℝ := fun κ =>
      ∫ x, ∑ i : Fin n, ‖gradient (fun y => gaussianRelativeScore n (ρ κ) y i) x‖ ^ 2 ∂ouInitialLaw n κ t
    (I ν + K ν + I η + K η) / (2 * (P : ℝ)) ≤
      ∫ p, matrixHilbertSchmidtSq (densityLogHessian n (ρ ν) p.1 - densityLogHessian n (ρ η) p.2)
        ∂(ouInitialLaw n ν t).prod (ouInitialLaw n η t) := by
  let E := EuclideanSpace ℝ (Fin n)
  let ρ : Measure E → E → ℝ := fun κ =>
    gaussianSmoothingDensity n κ (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  let I : Measure E → ℝ := fun κ => (relativeFisherMeasure n (ouInitialLaw n κ t)).toReal
  let K : Measure E → ℝ := fun κ =>
    ∫ x, ∑ i : Fin n, ‖gradient (fun y => gaussianRelativeScore n (ρ κ) y i) x‖ ^ 2 ∂ouInitialLaw n κ t
  let D := ∫ p : E × E, matrixHilbertSchmidtSq (densityLogHessian n (ρ ν) p.1 - densityLogHessian n (ρ η) p.2)
    ∂(ouInitialLaw n ν t).prod (ouInitialLaw n η t)
  have hd := (ou_smoothing_scale_domain t ht).2.1
  have hν : ouInitialLaw n ν t = densityMeasure n (ρ ν) := gaussianSmoothingDensity_law n ν _ _ hd
  have hη : ouInitialLaw n η t = densityMeasure n (ρ η) := gaussianSmoothingDensity_law n η _ _ hd
  have hIν : I ν = ∫ x, ‖gaussianRelativeScore n (ρ ν) x‖ ^ 2 ∂ouInitialLaw n ν t :=
    (ou_isotropic_relativeFisher_score_energy n ν hmeanν hcovν t ht).2
  have hIη : I η = ∫ x, ‖gaussianRelativeScore n (ρ η) x‖ ^ 2 ∂ouInitialLaw n η t :=
    (ou_isotropic_relativeFisher_score_energy n η hmeanη hcovη t ht).2
  have hfirst : (I ν + K η) / (P : ℝ) ≤ D := by
    have h := ou_relativeScore_product_regression n ν η hmeanν hcovν P hPone hPν t ht
    dsimp only at h
    simp_rw [vectorPoincareDerivativeMatrix_hilbertSchmidtSq] at h
    rw [← hν, ← hη, ← hIν] at h
    exact h
  have hsecond : (I η + K ν) / (P : ℝ) ≤ D := by
    have h := ou_relativeScore_product_regression n η ν hmeanη hcovη P hPone hPη t ht
    dsimp only at h
    simp_rw [vectorPoincareDerivativeMatrix_hilbertSchmidtSq] at h
    rw [← hη, ← hν, ← hIη] at h
    have hswap : (∫ p : E × E, matrixHilbertSchmidtSq
        (densityLogHessian n (ρ η) p.1 - densityLogHessian n (ρ ν) p.2)
        ∂(ouInitialLaw n η t).prod (ouInitialLaw n ν t)) = D := by
      rw [← integral_prod_swap (fun p : E × E => matrixHilbertSchmidtSq
        (densityLogHessian n (ρ η) p.1 - densityLogHessian n (ρ ν) p.2))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => matrixHilbertSchmidtSq_sub_comm n _ _
    rw [hswap] at h
    exact h
  have hPpos : (0 : ℝ) < (P : ℝ) := lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ (P : ℝ) from hPone)
  have hfirst' := (div_le_iff₀ hPpos).mp hfirst
  have hsecond' := (div_le_iff₀ hPpos).mp hsecond
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hPpos)).mpr
  linarith

theorem ou_convolution_hessian_regression_deficit (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f) (hg : Measurable g)
    [IsProbabilityMeasure (densityMeasure n f)] [IsProbabilityMeasure (densityMeasure n g)]
    (hlcf : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hlcg : LogConcaveDensity (fun x => ENNReal.ofReal (g x)))
    (hmeanν : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂densityMeasure n f) = 0)
    (hmeanη : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂densityMeasure n g) = 0)
    (hcovν : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂densityMeasure n f) =
      if i = j then (1 : ℝ) else 0)
    (hcovη : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂densityMeasure n g) =
      if i = j then (1 : ℝ) else 0)
    (P : ℝ≥0) (hPone : 1 ≤ P)
    (hPν : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (hPη : poincareConstant n (densityMeasure n g) ≤ (P : ℝ≥0∞))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (t : ℝ) (ht : 0 < t) :
    let ν := densityMeasure n f
    let η := densityMeasure n g
    let ξ := (ν.prod η).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2)
    let ρ : Measure (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) → ℝ :=
      fun κ => gaussianSmoothingDensity n κ (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    let I : Measure (EuclideanSpace ℝ (Fin n)) → ℝ := fun κ => (relativeFisherMeasure n (ouInitialLaw n κ t)).toReal
    let K : Measure (EuclideanSpace ℝ (Fin n)) → ℝ := fun κ =>
      ∫ x, ∑ i : Fin n, ‖gradient (fun y => gaussianRelativeScore n (ρ κ) y i) x‖ ^ 2 ∂ouInitialLaw n κ t
    a ^ 2 * (K ν + 2 * I ν) + b ^ 2 * (K η + 2 * I η) - (K ξ + 2 * I ξ) ≥
      (a ^ 2 * b ^ 2) / (2 * (P : ℝ)) * (I ν + K ν + I η + K η) := by
  let E := EuclideanSpace ℝ (Fin n)
  let ν := densityMeasure n f
  let η := densityMeasure n g
  let W : E × E → E := fun p => a • p.1 + b • p.2
  have hW : Measurable W := by dsimp [W]; fun_prop
  let ξ := (ν.prod η).map W
  let : IsProbabilityMeasure ξ := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let ρ : Measure E → E → ℝ := fun κ =>
    gaussianSmoothingDensity n κ (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  let I : Measure E → ℝ := fun κ => (relativeFisherMeasure n (ouInitialLaw n κ t)).toReal
  let K : Measure E → ℝ := fun κ =>
    ∫ x, ∑ i : Fin n, ‖gradient (fun y => gaussianRelativeScore n (ρ κ) y i) x‖ ^ 2 ∂ouInitialLaw n κ t
  let D := ∫ p : E × E, matrixHilbertSchmidtSq (densityLogHessian n (ρ ν) p.1 - densityLogHessian n (ρ η) p.2)
    ∂(ouInitialLaw n ν t).prod (ouInitialLaw n η t)
  have hξ := normalizedConvolution_isotropy n ν η hmeanν hmeanη hcovν hcovη a b hab
  have hmeanξ : ∀ i : Fin n, (∫ x : E, x i ∂ξ) = 0 := hξ.2.1
  have hcovξ : ∀ i j : Fin n, (∫ x : E, x i * x j ∂ξ) = if i = j then (1 : ℝ) else 0 := hξ.2.2
  have hKν : (∫ x, matrixHilbertSchmidtSq (densityLogHessian n (ρ ν) x) ∂ouInitialLaw n ν t) =
      K ν + 2 * I ν + n := ou_ordinary_hessian_eq_relative_energy n ν hmeanν hcovν t ht
  have hKη : (∫ x, matrixHilbertSchmidtSq (densityLogHessian n (ρ η) x) ∂ouInitialLaw n η t) =
      K η + 2 * I η + n := ou_ordinary_hessian_eq_relative_energy n η hmeanη hcovη t ht
  have hKξ : (∫ x, matrixHilbertSchmidtSq (densityLogHessian n (ρ ξ) x) ∂ouInitialLaw n ξ t) =
      K ξ + 2 * I ξ + n := ou_ordinary_hessian_eq_relative_energy n ξ hmeanξ hcovξ t ht
  have hdef := ou_normalized_convolution_hessian_deficit n f g hf hg hlcf hlcg a b ha hb hab t ht
  dsimp only at hdef
  rw [hKν, hKη, hKξ] at hdef
  change a ^ 2 * (K ν + 2 * I ν + n) + b ^ 2 * (K η + 2 * I η + n) - (K ξ + 2 * I ξ + n) ≥
    a ^ 2 * b ^ 2 * D at hdef
  have hreg : (I ν + K ν + I η + K η) / (2 * (P : ℝ)) ≤ D :=
    ou_relativeScore_pair_regression n ν η hmeanν hmeanη hcovν hcovη P hPone hPν hPη t ht
  have hmul := mul_le_mul_of_nonneg_left hreg (mul_nonneg (sq_nonneg a) (sq_nonneg b))
  have hbound : (a ^ 2 * b ^ 2) / (2 * (P : ℝ)) * (I ν + K ν + I η + K η) ≤ a ^ 2 * b ^ 2 * D := by
    calc
      _ = (a ^ 2 * b ^ 2) * ((I ν + K ν + I η + K η) / (2 * (P : ℝ))) := by ring
      _ ≤ _ := hmul
  have hn : a ^ 2 * (n : ℝ) + b ^ 2 * (n : ℝ) = n := by linear_combination (n : ℝ) * hab
  change a ^ 2 * (K ν + 2 * I ν) + b ^ 2 * (K η + 2 * I η) - (K ξ + 2 * I ξ) ≥
    (a ^ 2 * b ^ 2) / (2 * (P : ℝ)) * (I ν + K ν + I η + K η)
  linarith

end AffineFKProof
