module

public import AffineFK.GaussianPositionTiltMeanMap
public import AffineFK.InjectiveJacobianIntegral
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Actual log-Laplace Jacobian mass and selection of a small determinant

The genuine gradient is injective and belongs to the original compact
convex body. Its proved Frechet derivatives therefore satisfy the actual
change-of-variables bound, with integrability derived from finite image
volume. No Jacobian integral or small-determinant point is assumed.

Mathlib's first moment method selects a point below the actual average.
A dimension-independent lower volume bound for the dilated polar would
then give a dimension-exponential determinant bound. The reverse
volume-product theorem needed for that geometric input is separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped ENNReal

theorem gaussianPositionLogLaplace_jacobian_integral_bound (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hvol : 0 < volume K)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U) :
    IntegrableOn (fun y => |(fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y).det|) U volume ∧
      (∫ y in U, |(fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y).det| ∂volume) =
        volume.real (gradient (gaussianPositionLogLaplace n K) '' U) ∧
      (∫ y in U, |(fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y).det| ∂volume) ≤
        volume.real K := by
  apply injective_jacobian_integral_bound_of_hasFDerivAt n
    (gradient (gaussianPositionLogLaplace n K))
    (fderiv ℝ (gradient (gaussianPositionLogLaplace n K))) U K hU
  · intro y _hy
    exact (gaussianPositionLogLaplace_gradient_differentiableAt n K hK hvol y).hasFDerivAt
  · exact (gaussianPositionLogLaplace_gradient_injective n K hK hvol).injOn
  · rintro z ⟨y, _hy, rfl⟩
    exact gaussianPositionLogLaplace_gradient_mem n K hK hconv hvol y
  · exact hK.measure_lt_top.ne

theorem gaussianPositionLogLaplace_global_jacobian_integral_bound (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hvol : 0 < volume K) :
    Integrable (fun y => |(fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y).det|) volume ∧
      (∫ y, |(fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y).det| ∂volume) =
        volume.real (range (gradient (gaussianPositionLogLaplace n K))) ∧
      (∫ y, |(fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y).det| ∂volume) ≤
        volume.real K := by
  simpa only [IntegrableOn, Measure.restrict_univ, image_univ] using
    gaussianPositionLogLaplace_jacobian_integral_bound n K hK hconv hvol univ MeasurableSet.univ

theorem gaussianPositionLogLaplace_exists_small_jacobian (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hvol : 0 < volume K)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hUpos : 0 < volume U) (hUfinite : volume U ≠ ∞) :
    ∃ y ∈ U, |(fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y).det| ≤
      volume.real K / volume.real U := by
  obtain ⟨hInt,_hExact,hBound⟩ :=
    gaussianPositionLogLaplace_jacobian_integral_bound n K hK hconv hvol U hU
  obtain ⟨y,hy,hMean⟩ := exists_le_setAverage hUpos.ne' hUfinite hInt
  rw [setAverage_eq, smul_eq_mul] at hMean
  refine ⟨y,hy,hMean.trans ?_⟩
  have hInv : 0 ≤ (volume.real U)⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  calc
    _ ≤ (volume.real U)⁻¹ * volume.real K := mul_le_mul_of_nonneg_left hBound hInv
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

theorem gaussianPositionLogLaplace_exists_small_jacobian_of_volume_lower (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hvolK : volume K = 1)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hUfinite : volume U ≠ ∞) (b : ℝ) (hb : 0 < b)
    (hUlower : b ^ n ≤ volume.real U) :
    ∃ y ∈ U, |(fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y).det| ≤ (b⁻¹) ^ n := by
  have hUreal : 0 < volume.real U := (pow_pos hb n).trans_le hUlower
  have hUpos : 0 < volume U := ENNReal.toReal_pos_iff.mp hUreal |>.1
  have hKpos : 0 < volume K := by rw [hvolK]; exact zero_lt_one
  obtain ⟨y,hy,hsmall⟩ := gaussianPositionLogLaplace_exists_small_jacobian
    n K hK hconv hKpos U hU hUpos hUfinite
  have hKreal : volume.real K = 1 := by rw [measureReal_def,hvolK,ENNReal.toReal_one]
  rw [hKreal,one_div] at hsmall
  refine ⟨y,hy,hsmall.trans ?_⟩
  rw [inv_pow]
  exact (inv_le_inv₀ hUreal (pow_pos hb n)).mpr hUlower

end AffineFKProof
