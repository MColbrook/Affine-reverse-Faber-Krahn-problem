module

public import AffineFK.GaussianPositionTiltLaw
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Differentiating genuine tilted moments

Every continuous observable on the compact body is integrable under the
actual tilted probability law. Differentiation of its genuine integral
gives its covariance with the linear statistic, without an assumed
moment or Hessian formula. The local exponential majorant is derived
before using Mathlib's dominated parameter differentiation theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace Topology

def gaussianPositionTiltMoment (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x in K, Real.exp ⟪x, y⟫ * f x

theorem gaussianPositionTiltMoment_hasFDerivAt (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gaussianPositionTiltMoment n K f)
      (∫ x in K, f x • gaussianPositionTiltDerivative n y x) y := by
  let E := EuclideanSpace ℝ (Fin n)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball y 1)
    (bound := fun x : E => ‖f x‖ * (Real.exp (‖x‖ * (‖y‖ + 1)) * ‖x‖))
    (ball_mem_nhds y zero_lt_one)
  · exact Eventually.of_forall fun z =>
      ((Real.continuous_exp.comp (continuous_id.inner continuous_const)).mul hf).aestronglyMeasurable
  · exact ContinuousOn.integrableOn_compact hK
      ((Real.continuous_exp.comp (continuous_id.inner continuous_const)).mul hf).continuousOn
  · exact (hf.smul (gaussianPositionTiltDerivative_continuous n y)).aestronglyMeasurable
  · exact Eventually.of_forall fun x z hz => by
      have hzy : ‖z‖ ≤ ‖y‖ + 1 := (norm_lt_of_mem_ball hz).le
      have hinner : ⟪x, z⟫ ≤ ‖x‖ * (‖y‖ + 1) :=
        (real_inner_le_norm x z).trans (mul_le_mul_of_nonneg_left hzy (norm_nonneg x))
      simp only [gaussianPositionTiltDerivative, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hinner) (norm_nonneg x)) (abs_nonneg _)
  · exact ContinuousOn.integrableOn_compact hK
      (hf.norm.mul ((Real.continuous_exp.comp
        (continuous_norm.mul continuous_const)).mul continuous_norm)).continuousOn
  · exact Eventually.of_forall fun x z _ =>
      (((InnerProductSpace.toDual ℝ E x).hasFDerivAt).exp).mul_const (f x)

theorem gaussianPositionTiltMoment_derivative_apply (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (y v : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (gaussianPositionTiltMoment n K f) y) v =
      ∫ x in K, Real.exp ⟪x, y⟫ * (f x * ⟪x, v⟫) := by
  rw [(gaussianPositionTiltMoment_hasFDerivAt n K hK f hf y).fderiv,
    ContinuousLinearMap.integral_apply (φ := fun x => f x • gaussianPositionTiltDerivative n y x)
      (ContinuousOn.integrableOn_compact hK
      (hf.smul (gaussianPositionTiltDerivative_continuous n y)).continuousOn)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [gaussianPositionTiltDerivative, smul_apply, smul_eq_mul,
      InnerProductSpace.toDual_apply_apply]
    ring

theorem gaussianPositionTiltLaw_expectation_hasFDerivAt (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z => ∫ x, f x ∂gaussianPositionTiltLaw n K z)
      ((gaussianPositionTiltPartition n K y)⁻¹ •
          (∫ x in K, f x • gaussianPositionTiltDerivative n y x) +
        gaussianPositionTiltMoment n K f y •
          (-((gaussianPositionTiltPartition n K y) ^ 2)⁻¹ •
            (∫ x in K, gaussianPositionTiltDerivative n y x))) y := by
  have heq : (fun z => ∫ x, f x ∂gaussianPositionTiltLaw n K z) =
      (fun z => (gaussianPositionTiltPartition n K z)⁻¹ * gaussianPositionTiltMoment n K f z) :=
    funext fun z => gaussianPositionTiltLaw_integral n K hK hvol z f
  rw [heq]
  exact ((hasDerivAt_inv (gaussianPositionTiltPartition_pos n K hK hvol y).ne').comp_hasFDerivAt y
    (gaussianPositionTiltPartition_hasFDerivAt n K hK y)).mul
      (gaussianPositionTiltMoment_hasFDerivAt n K hK f hf y)

theorem gaussianPositionTiltLaw_derivative_covariance (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (y v : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (fun z => ∫ x, f x ∂gaussianPositionTiltLaw n K z) y) v =
      (∫ x, f x * ⟪x, v⟫ ∂gaussianPositionTiltLaw n K y) -
        (∫ x, f x ∂gaussianPositionTiltLaw n K y) *
          (∫ x, ⟪x, v⟫ ∂gaussianPositionTiltLaw n K y) := by
  have hZ := (gaussianPositionTiltPartition_pos n K hK hvol y).ne'
  rw [(gaussianPositionTiltLaw_expectation_hasFDerivAt n K hK hvol f hf y).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have hM : (∫ x in K, f x • gaussianPositionTiltDerivative n y x) v =
      ∫ x in K, Real.exp ⟪x, y⟫ * (f x * ⟪x, v⟫) := by
    rw [← (gaussianPositionTiltMoment_hasFDerivAt n K hK f hf y).fderiv]
    exact gaussianPositionTiltMoment_derivative_apply n K hK f hf y v
  have hD : (∫ x in K, gaussianPositionTiltDerivative n y x) v =
      ∫ x in K, Real.exp ⟪x, y⟫ * ⟪x, v⟫ := by
    rw [← (gaussianPositionTiltPartition_hasFDerivAt n K hK y).fderiv]
    exact gaussianPositionTiltPartition_derivative_apply n K hK y v
  rw [hM, hD, gaussianPositionTiltLaw_integral n K hK hvol y,
    gaussianPositionTiltLaw_integral n K hK hvol y,
    gaussianPositionTiltLaw_integral n K hK hvol y]
  dsimp only [gaussianPositionTiltMoment]
  field_simp
  ring

theorem gaussianPositionLogLaplace_second_derivative_covariance (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y u v : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (fun z => (fderiv ℝ (gaussianPositionLogLaplace n K) z) u) y) v =
      (∫ x, ⟪x, u⟫ * ⟪x, v⟫ ∂gaussianPositionTiltLaw n K y) -
        (∫ x, ⟪x, u⟫ ∂gaussianPositionTiltLaw n K y) *
          (∫ x, ⟪x, v⟫ ∂gaussianPositionTiltLaw n K y) := by
  have heq : (fun z => (fderiv ℝ (gaussianPositionLogLaplace n K) z) u) =
      (fun z => ∫ x, ⟪x, u⟫ ∂gaussianPositionTiltLaw n K z) :=
    funext fun z => gaussianPositionLogLaplace_derivative_apply n K hK hvol z u
  rw [heq]
  exact gaussianPositionTiltLaw_derivative_covariance n K hK hvol
    (fun x => ⟪x, u⟫) (continuous_id.inner continuous_const) y v

end AffineFKProof
