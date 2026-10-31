module

public import AffineFK.GaussianPositionTiltHessian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Probability.Moments.Variance

/-!
# Strict positivity of the genuine tilted covariance Hessian

Absolute continuity of the actual tilted law excludes every nontrivial
affine hyperplane. A zero variance would concentrate the probability law
on one such null hyperplane. Thus the actual Hessian is positive in every
nonzero direction; this is derived rather than supplied as a premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

theorem gaussianPositionTiltLaw_absolutelyContinuous (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n)) :
    gaussianPositionTiltLaw n K y ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

theorem gaussianPositionTiltLaw_continuous_memLp_two (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) :
    MemLp f 2 (gaussianPositionTiltLaw n K y) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  exact gaussianPositionTiltLaw_continuous_integrable n K hK hvol y (fun x => (f x)^2) (hf.pow 2)

theorem gaussianPosition_linear_level_volume_zero (n : ℕ)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) (c : ℝ) :
    volume {x : EuclideanSpace ℝ (Fin n) | ⟪x, v⟫ = c} = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E v
  have hker : L.toLinearMap.ker ≠ ⊤ := by
    intro h
    have hmem : v ∈ L.toLinearMap.ker := by rw [h]; trivial
    change ⟪v, v⟫ = 0 at hmem
    exact hv (inner_self_eq_zero.mp hmem)
  let w : E := (c / ‖v‖^2) • v
  have hw : ⟪w, v⟫ = c := by
    dsimp only [w]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ c (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))
  have hset : {x : E | ⟪x, v⟫ = c} =
      (fun x : E => x + -w) ⁻¹' (L.toLinearMap.ker : Set E) := by
    ext x
    change ⟪x, v⟫ = c ↔ L (x + -w) = 0
    simp only [L, InnerProductSpace.toDual_apply_apply, inner_add_right, inner_neg_right]
    rw [real_inner_comm w v, hw, real_inner_comm x v]
    constructor <;> intro h <;> linarith
  rw [hset, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ hker

theorem gaussianPositionTiltLaw_linear_variance_pos (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < variance (fun x => ⟪x, v⟫) (gaussianPositionTiltLaw n K y) := by
  let μ := gaussianPositionTiltLaw n K y
  let : IsProbabilityMeasure μ := gaussianPositionTiltLaw_isProbabilityMeasure n K hK hvol y
  have hF := gaussianPositionTiltLaw_continuous_memLp_two n K hK hvol y
    (fun x => ⟪x, v⟫) (continuous_id.inner continuous_const)
  have hnull (c : ℝ) : μ {x | ⟪x, v⟫ = c} = 0 :=
    gaussianPositionTiltLaw_absolutelyContinuous n K y (gaussianPosition_linear_level_volume_zero n v hv c)
  by_contra hpos
  have hzero : variance (fun x => ⟪x, v⟫) μ = 0 :=
    le_antisymm (le_of_not_gt hpos) (variance_nonneg _ _)
  have hae := ae_eq_integral_of_variance_eq_zero hF hzero
  have hfull := (ae_mem_iff_measure_eq
    ((continuous_id.inner continuous_const).measurable
      (measurableSet_singleton (∫ x, ⟪x, v⟫ ∂μ))).nullMeasurableSet).mp hae
  change μ {x | ⟪x, v⟫ = ∫ z, ⟪z, v⟫ ∂μ} = μ univ at hfull
  rw [hnull, measure_univ] at hfull
  exact zero_ne_one hfull

theorem gaussianPositionLogLaplace_hessian_positive (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < ((fderiv ℝ (fderiv ℝ (gaussianPositionLogLaplace n K)) y) v) v := by
  let : IsProbabilityMeasure (gaussianPositionTiltLaw n K y) :=
    gaussianPositionTiltLaw_isProbabilityMeasure n K hK hvol y
  have hF := gaussianPositionTiltLaw_continuous_memLp_two n K hK hvol y
    (fun x => ⟪x, v⟫) (continuous_id.inner continuous_const)
  have h := gaussianPositionTiltLaw_linear_variance_pos n K hK hvol y v hv
  rw [variance_eq_sub hF] at h
  rw [gaussianPositionLogLaplace_hessian_covariance n K hK hvol y v v]
  simpa only [Pi.pow_apply, pow_two] using h

end AffineFKProof
