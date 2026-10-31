module

public import AffineFK.GaussianPositionTiltLaw
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.LocallyConvex.Polar

/-!
# Uniform bounds for actual bounded exponential tilts

For a volume-one compact origin-symmetric body Jensen gives Lambda>=0.
On the actual dilated polar n K^polar, the support bound gives Lambda<=n
and exp(-2n)<=rho_y<=exp(n) on K. These constants follow directly from
-n<=inner(x,y)<=n and 0<=Lambda<=n; no density-bound formula is assumed.
This is the elementary part of Klartag ETH 2025 Lecture 7 Proposition 7.2.
The volume-product/determinant-existence step remains separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped RealInnerProductSpace Pointwise ENNReal

def gaussianPositionTiltDensity (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (y x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  K.indicator (fun z => (gaussianPositionTiltPartition n K y)⁻¹ * Real.exp ⟪z, y⟫) x

theorem gaussianPositionTiltDensity_measurable (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (y : EuclideanSpace ℝ (Fin n)) : Measurable (gaussianPositionTiltDensity n K y) :=
  (measurable_const.mul (Real.continuous_exp.comp
    (continuous_id.inner continuous_const)).measurable).indicator hK

theorem gaussianPositionTiltDensity_law (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (y : EuclideanSpace ℝ (Fin n)) :
    densityMeasure n (gaussianPositionTiltDensity n K y) = gaussianPositionTiltLaw n K y := by
  classical
  have heq : (fun x => ENNReal.ofReal (gaussianPositionTiltDensity n K y x)) =
      K.indicator (fun x => ENNReal.ofReal
        ((gaussianPositionTiltPartition n K y)⁻¹ * Real.exp ⟪x, y⟫)) := by
    funext x
    by_cases hx : x ∈ K <;> simp [gaussianPositionTiltDensity, hx]
  rw [densityMeasure, heq, withDensity_indicator hK]
  rfl

theorem gaussianPosition_uniform_linear_mean_zero (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (heven : ∀ x, -x ∈ K ↔ x ∈ K) (y : EuclideanSpace ℝ (Fin n)) :
    (∫ x in K, ⟪x, y⟫) = 0 := by
  classical
  have hodd (x : EuclideanSpace ℝ (Fin n)) :
      K.indicator (fun z => ⟪z, y⟫) (-x) = -K.indicator (fun z => ⟪z, y⟫) x := by
    by_cases hx : x ∈ K
    · simp only [indicator_of_mem hx, indicator_of_mem ((heven x).mpr hx), inner_neg_left]
    · simp only [indicator_of_notMem hx,
        indicator_of_notMem (fun h => hx ((heven x).mp h)), neg_zero]
  have h := integral_neg_eq_self (K.indicator (fun x => ⟪x, y⟫)) volume
  simp_rw [hodd, integral_neg] at h
  rw [integral_indicator hK] at h
  linarith

theorem gaussianPositionLogLaplace_nonneg (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hvolume : volume K = 1) (heven : ∀ x, -x ∈ K ↔ x ∈ K)
    (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ gaussianPositionLogLaplace n K y := by
  let : IsProbabilityMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hvolume⟩
  have hJ := ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _)
    (ContinuousOn.integrableOn_compact hK (continuous_id.inner continuous_const).continuousOn)
    (gaussianPositionTilt_integrable n K hK y)
  simp only [id_eq] at hJ
  rw [gaussianPosition_uniform_linear_mean_zero n K hK.measurableSet heven y, Real.exp_zero] at hJ
  exact Real.log_nonneg hJ

theorem gaussianPositionLogLaplace_le_of_support (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvolume : volume K = 1)
    (y : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : ∀ x ∈ K, ⟪x, y⟫ ≤ R) :
    gaussianPositionLogLaplace n K y ≤ R := by
  let : IsProbabilityMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hvolume⟩
  have hpos : 0 < volume K := by rw [hvolume]; exact zero_lt_one
  have hbound : gaussianPositionTiltPartition n K y ≤ Real.exp R := by
    have h := integral_mono_ae (gaussianPositionTilt_integrable n K hK y)
      (integrable_const (Real.exp R))
      (ae_restrict_of_forall_mem hK.measurableSet fun x hx => Real.exp_le_exp.mpr (hR x hx))
    simpa only [gaussianPositionTiltPartition, integral_const, probReal_univ, one_smul] using h
  have h := Real.log_le_log (gaussianPositionTiltPartition_pos n K hK hpos y) hbound
  rwa [Real.log_exp] at h

theorem gaussianPosition_dilated_polar_inner_bound (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ (n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) :
    ∀ x ∈ K, |⟪x, y⟫| ≤ (n : ℝ) := by
  rcases hy with ⟨z, hz, rfl⟩
  intro x hx
  have h := hz x hx
  simp only [innerₗ_apply_apply, Real.norm_eq_abs] at h
  rw [inner_smul_right, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)).trans_eq (mul_one _)

theorem gaussianPositionTiltDensity_dilated_polar_bounds (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hvolume : volume K = 1) (heven : ∀ x, -x ∈ K ↔ x ∈ K)
    (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ (n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) :
    0 ≤ gaussianPositionLogLaplace n K y ∧ gaussianPositionLogLaplace n K y ≤ n ∧
      ∀ x ∈ K, Real.exp (-2 * (n : ℝ)) ≤ gaussianPositionTiltDensity n K y x ∧
        gaussianPositionTiltDensity n K y x ≤ Real.exp (n : ℝ) := by
  have hinner := gaussianPosition_dilated_polar_inner_bound n K y hy
  have hlow := gaussianPositionLogLaplace_nonneg n K hK hvolume heven y
  have hupp := gaussianPositionLogLaplace_le_of_support n K hK hvolume y n
    (fun x hx => (le_abs_self _).trans (hinner x hx))
  have hpos : 0 < volume K := by rw [hvolume]; exact zero_lt_one
  have hZ := gaussianPositionTiltPartition_pos n K hK hpos y
  refine ⟨hlow, hupp, ?_⟩
  intro x hx
  have heq : gaussianPositionTiltDensity n K y x =
      Real.exp (⟪x, y⟫ - gaussianPositionLogLaplace n K y) := by
    rw [gaussianPositionTiltDensity, indicator_of_mem hx, Real.exp_sub,
      gaussianPositionLogLaplace, Real.exp_log hZ]
    ring
  rw [heq]
  constructor
  · apply Real.exp_le_exp.mpr
    have h := (abs_le.mp (hinner x hx)).1
    linarith
  · apply Real.exp_le_exp.mpr
    have h := (abs_le.mp (hinner x hx)).2
    linarith

end AffineFKProof
