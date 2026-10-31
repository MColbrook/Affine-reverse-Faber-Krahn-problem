module

public import AffineFK.WhitenedConvolutionBounds
public import AffineFK.ProbabilityLinearCovariance
public import AffineFK.ProbabilitySumCovariance

/-!
# Isotropy of the actual covariance-whitened convolution

The two input means and second moments identify the covariance of their
literal independent sum. The proved inverse-square-root matrix identity
then gives the identity covariance of the actual image law. No output
moment or isotropy condition is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem whitenedSumLaw_eq_linear_image (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) (α : ℝ) :
    whitenedSumLaw n ν η α =
      ((ν.prod η).map (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 + p.2)).map
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
          (covarianceWhiteningMatrix n (convolutionCovarianceMatrix n α η))) := by
  rw [Measure.map_map (ContinuousLinearMap.continuous _).measurable (by fun_prop)]
  rfl

theorem whitenedSumLaw_isProbabilityMeasure (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (α : ℝ) : IsProbabilityMeasure (whitenedSumLaw n ν η α) := by
  apply (Measure.isProbabilityMeasure_map_iff ?_).mpr inferInstance
  exact (show Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (covarianceWhiteningMatrix n (convolutionCovarianceMatrix n α η)) (p.1 + p.2)) by fun_prop).aemeasurable

theorem whitenedSumLaw_isotropic (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 η)
    (hmeanX : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hmeanY : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂η) = 0)
    (hPη : poincareConstant n η ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hcovX : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) =
      if i = j then α else 0) :
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (whitenedSumLaw n ν η α) ∧
      (∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂whitenedSumLaw n ν η α) = 0) ∧
      (∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂whitenedSumLaw n ν η α) =
        if i = j then 1 else 0) := by
  let E := EuclideanSpace ℝ (Fin n)
  let κ := (ν.prod η).map (fun p : E × E => p.1 + p.2)
  have hsum : Measurable (fun p : E × E => p.1 + p.2) := by fun_prop
  let : IsProbabilityMeasure κ := (Measure.isProbabilityMeasure_map_iff hsum.aemeasurable).mpr inferInstance
  let M := convolutionCovarianceMatrix n α η
  let W := covarianceWhiteningMatrix n M
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) W
  have hκ := probability_sum_covariance_scalar_left n ν η hX hY hmeanX hmeanY α hcovX
  have hlaw : whitenedSumLaw n ν η α = κ.map T := whitenedSumLaw_eq_linear_image n ν η α
  have hM : M.PosDef := (convolutionCovarianceMatrix_bounds n η hY hmeanY hPη α hα hαone).2.2
  rw [hlaw]
  refine ⟨(memLp_map_measure_iff aestronglyMeasurable_id T.continuous.measurable.aemeasurable).mpr
    (T.comp_memLp' hκ.1), ?_, ?_⟩
  · exact probability_linear_image_mean_zero n κ hκ.1 hκ.2.1 W
  · have hC : probabilitySecondMomentMatrix n (κ.map T) = 1 := by
      rw [probabilitySecondMomentMatrix_linear_image n κ hκ.1 W, hκ.2.2]
      exact covarianceWhiteningMatrix_identity n M hM
    intro i j
    have h := congrArg (fun C : Matrix (Fin n) (Fin n) ℝ => C i j) hC
    simpa only [probabilitySecondMomentMatrix, Matrix.one_apply] using h

end AffineFKProof
