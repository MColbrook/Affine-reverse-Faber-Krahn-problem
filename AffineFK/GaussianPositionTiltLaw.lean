module

public import AffineFK.GaussianPositionTiltCalculus
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Actual normalized exponential tilts and their mean

The law is the actual withDensity measure on the compact domain, normalized
by its proved positive partition integral. Its gradient is the actual
tilted mean. No probability normalization or mean formula is assumed.
The classical formulas are those of the logarithmic Laplace transform;
Mathlib's genuine withDensity, Bochner integral and Frechet-Riesz APIs
provide the measure/integration steps, with their retained attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

def gaussianPositionTiltLaw (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (volume.restrict K).withDensity (fun x => ENNReal.ofReal
    ((gaussianPositionTiltPartition n K y)⁻¹ * Real.exp ⟪x, y⟫))

theorem gaussianPositionTiltLaw_isProbabilityMeasure (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) : IsProbabilityMeasure (gaussianPositionTiltLaw n K y) := by
  have hZ := gaussianPositionTiltPartition_pos n K hK hvol y
  have hInt := (gaussianPositionTilt_integrable n K hK y).const_mul
    (gaussianPositionTiltPartition n K y)⁻¹
  rw [isProbabilityMeasure_iff, gaussianPositionTiltLaw,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall fun x =>
      mul_nonneg (inv_nonneg.mpr hZ.le) (Real.exp_pos _).le), integral_const_mul]
  change ENNReal.ofReal ((gaussianPositionTiltPartition n K y)⁻¹ *
    gaussianPositionTiltPartition n K y) = 1
  rw [inv_mul_cancel₀ hZ.ne', ENNReal.ofReal_one]

theorem gaussianPositionTiltLaw_integral (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f x ∂gaussianPositionTiltLaw n K y) =
      (gaussianPositionTiltPartition n K y)⁻¹ * (∫ x in K, Real.exp ⟪x, y⟫ * f x) := by
  have hZ := gaussianPositionTiltPartition_pos n K hK hvol y
  have hw : Measurable (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      ((gaussianPositionTiltPartition n K y)⁻¹ * Real.exp ⟪x, y⟫)) := by
    fun_prop
  rw [gaussianPositionTiltLaw,
    integral_withDensity_eq_integral_toReal_smul hw
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
  simp only [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hZ.le) (Real.exp_pos _).le),
    smul_eq_mul, mul_assoc, integral_const_mul]

theorem gaussianPositionTiltLaw_continuous_integrable (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin n) → F) (hf : Continuous f) :
    Integrable f (gaussianPositionTiltLaw n K y) := by
  have hZ := gaussianPositionTiltPartition_pos n K hK hvol y
  have hw : Measurable (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      ((gaussianPositionTiltPartition n K y)⁻¹ * Real.exp ⟪x, y⟫)) := by
    fun_prop
  rw [gaussianPositionTiltLaw,
    integrable_withDensity_iff_integrable_smul' hw
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hZ.le) (Real.exp_pos _).le)]
  exact ContinuousOn.integrableOn_compact hK
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_id.inner continuous_const))).smul hf).continuousOn

theorem gaussianPositionLogLaplace_derivative_apply (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y v : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (gaussianPositionLogLaplace n K) y) v =
      ∫ x, ⟪x, v⟫ ∂gaussianPositionTiltLaw n K y := by
  rw [(gaussianPositionLogLaplace_hasFDerivAt n K hK hvol y).fderiv,
    smul_apply, smul_eq_mul,
    gaussianPositionTiltLaw_integral n K hK hvol y]
  congr 1
  rw [ContinuousLinearMap.integral_apply (ContinuousOn.integrableOn_compact hK
    (gaussianPositionTiltDerivative_continuous n y).continuousOn)]
  rfl

theorem gaussianPositionLogLaplace_gradient_mean (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) :
    gradient (gaussianPositionLogLaplace n K) y =
      ∫ x, x ∂gaussianPositionTiltLaw n K y := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left (𝕜 := ℝ), gaussianPositionLogLaplace_derivative_apply n K hK hvol y]
  simpa only [real_inner_comm, id_eq] using integral_inner (𝕜 := ℝ)
    (gaussianPositionTiltLaw_continuous_integrable n K hK hvol y id continuous_id) v

end AffineFKProof
