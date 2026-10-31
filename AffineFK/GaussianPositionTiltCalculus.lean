module

public import AffineFK.GaussianPositionIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The genuine compact-domain exponential partition integral

The partition function and logarithmic Laplace transform are literal
Lebesgue integrals. Parameter differentiation uses a local exponential
majorant integrable on the actual compact domain. This supplies part of
the analytic route in Klartag's ETH 2025 Lecture 7, Proposition 7.1;
no volume-product or M-ellipsoid existence theorem is assumed.

The dominated differentiation theorem is Mathlib's theorem of Patrick
Massot. The proof follows the fixed-domain differentiation pattern in
GaussianPositionIntegral, with an explicitly derived local bound.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace Topology

def gaussianPositionTiltPartition (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x in K, Real.exp ⟪x, y⟫

def gaussianPositionLogLaplace (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.log (gaussianPositionTiltPartition n K y)

def gaussianPositionTiltDerivative (n : ℕ)
    (y x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  Real.exp ⟪x, y⟫ • InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) x

theorem gaussianPositionTilt_integrable (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (y : EuclideanSpace ℝ (Fin n)) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪x, y⟫) K :=
  ContinuousOn.integrableOn_compact hK
    (Real.continuous_exp.comp (continuous_id.inner continuous_const)).continuousOn

theorem gaussianPositionTiltDerivative_continuous (n : ℕ)
    (y : EuclideanSpace ℝ (Fin n)) :
    Continuous (gaussianPositionTiltDerivative n y) := by
  exact (Real.continuous_exp.comp (continuous_id.inner continuous_const)).smul
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).continuous

theorem gaussianPositionTiltPartition_hasFDerivAt (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gaussianPositionTiltPartition n K)
      (∫ x in K, gaussianPositionTiltDerivative n y x) y := by
  let E := EuclideanSpace ℝ (Fin n)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball y 1) (bound := fun x : E => Real.exp (‖x‖ * (‖y‖ + 1)) * ‖x‖)
    (ball_mem_nhds y zero_lt_one)
  · exact Eventually.of_forall fun z =>
      (Real.continuous_exp.comp (continuous_id.inner continuous_const)).aestronglyMeasurable
  · exact gaussianPositionTilt_integrable n K hK y
  · exact (gaussianPositionTiltDerivative_continuous n y).aestronglyMeasurable
  · exact Eventually.of_forall fun x z hz => by
      have hzy : ‖z‖ ≤ ‖y‖ + 1 := (norm_lt_of_mem_ball hz).le
      have hinner : ⟪x, z⟫ ≤ ‖x‖ * (‖y‖ + 1) :=
        (real_inner_le_norm x z).trans (mul_le_mul_of_nonneg_left hzy (norm_nonneg x))
      simp only [gaussianPositionTiltDerivative, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hinner) (norm_nonneg x)
  · exact ContinuousOn.integrableOn_compact hK
      ((Real.continuous_exp.comp (continuous_norm.mul continuous_const)).mul continuous_norm).continuousOn
  · exact Eventually.of_forall fun x z _ => by
      exact ((InnerProductSpace.toDual ℝ E x).hasFDerivAt).exp

theorem gaussianPositionTiltPartition_pos (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) : 0 < gaussianPositionTiltPartition n K y := by
  have hsupp : Function.support (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪x, y⟫) = univ := by
    ext x
    simp only [Function.mem_support, ne_eq, Real.exp_ne_zero, not_false_eq_true, mem_univ]
  apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos ⟪x, y⟫).le)
    (gaussianPositionTilt_integrable n K hK y)).mpr
  simpa only [hsupp, Measure.restrict_apply_univ] using hvol

theorem gaussianPositionLogLaplace_hasFDerivAt (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gaussianPositionLogLaplace n K)
      ((gaussianPositionTiltPartition n K y)⁻¹ •
        (∫ x in K, gaussianPositionTiltDerivative n y x)) y :=
  (gaussianPositionTiltPartition_hasFDerivAt n K hK y).log
    (gaussianPositionTiltPartition_pos n K hK hvol y).ne'

theorem gaussianPositionTiltPartition_derivative_apply (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (y v : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (gaussianPositionTiltPartition n K) y) v =
      ∫ x in K, Real.exp ⟪x, y⟫ * ⟪x, v⟫ := by
  rw [(gaussianPositionTiltPartition_hasFDerivAt n K hK y).fderiv,
    ContinuousLinearMap.integral_apply (ContinuousOn.integrableOn_compact hK
      (gaussianPositionTiltDerivative_continuous n y).continuousOn)]
  rfl

end AffineFKProof
