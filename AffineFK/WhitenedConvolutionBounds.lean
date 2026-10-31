module

public import AffineFK.ConvolutionCovarianceWhitening
public import AffineFK.PoincareConstantLinearMap
public import AffineFK.OrdinaryFisherConvolutionMeasure
public import AffineFK.OrdinaryFisherLinearMapMeasure

/-!
# Actual Poincare and ordinary information bounds after covariance whitening

The map is the inverse square root constructed from alpha Id plus the
actual second-moment matrix of the second law. The norm bounds are proved
from its genuine Poincare inequality and moments; convolution and linear
transport then give bounds for the actual image law. No information
finiteness is needed for the extended ordinary inequality.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ENNReal

def whitenedSumLaw (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n))) (α : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (ν.prod η).map (fun p =>
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (covarianceWhiteningMatrix n (convolutionCovarianceMatrix n α η)) (p.1 + p.2))

theorem whitenedSumLaw_poincare_fisher_bounds (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 η)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂η) = 0)
    (hPν : poincareConstant n ν ≤ 1) (hPη : poincareConstant n η ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1) :
    poincareConstant n (whitenedSumLaw n ν η α) ≤ ENNReal.ofReal (2 / α) ∧
      ordinaryFisherMeasure n (whitenedSumLaw n ν η α) ≤ 2 * ordinaryFisherMeasure n η := by
  let E := EuclideanSpace ℝ (Fin n)
  let κ := (ν.prod η).map (fun p : E × E => p.1 + p.2)
  have hsum : Measurable (fun p : E × E => p.1 + p.2) := by fun_prop
  let : IsProbabilityMeasure κ := (Measure.isProbabilityMeasure_map_iff hsum.aemeasurable).mpr inferInstance
  have hb := convolutionCovarianceMatrix_bounds n η hY hmean hPη α hα hαone
  let A := covarianceWhiteningLinear n (convolutionCovarianceMatrix n α η) hb.2.2
  have hAN : ‖A.toContinuousLinearMap‖ ^ 2 ≤ α⁻¹ :=
    covarianceWhiteningLinear_norm_sq_bound n _ hb.2.2 α hα hb.1
  have hAIN : ‖A.symm.toContinuousLinearMap‖ ^ 2 ≤ 2 :=
    covarianceWhiteningLinear_inverse_norm_sq_bound n _ hb.2.2 hb.2.1
  have hlaw : whitenedSumLaw n ν η α = κ.map A := by
    rw [Measure.map_map A.continuous.measurable hsum]
    rfl
  have hκP : poincareConstant n κ ≤ 2 := by
    exact (poincareConstant_convolution n ν η).trans
      (by simpa only [one_add_one_eq_two] using add_le_add hPν hPη)
  have hκJ := ordinaryFisherMeasure_convolution n ν η
  rw [hlaw]
  constructor
  · calc
      _ ≤ ENNReal.ofReal (‖A.toContinuousLinearMap‖ ^ 2) * poincareConstant n κ :=
        poincareConstant_linearMap n n κ A.toContinuousLinearMap
      _ ≤ ENNReal.ofReal α⁻¹ * 2 := mul_le_mul' (ENNReal.ofReal_le_ofReal hAN) hκP
      _ = ENNReal.ofReal (2 / α) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hα.le)]
        congr 1
        rw [div_eq_mul_inv, mul_comm]
  · exact (ordinaryFisherMeasure_linearMap n κ A).trans
      (mul_le_mul' (by simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hAIN) hκJ)

end AffineFKProof
