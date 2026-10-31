module

public import AffineFK.GaussianPositionBall
public import AffineFK.GaussianPositionMassCovariance

/-!
# Gaussian mass from a literal intersection with a volume-one ball

The actual Gaussian density is bounded below on the ball by its explicit
quadratic formula. Integration over the actual intersection gives the
dimension-exponential lower mass estimate. The intersection volume is an
input, not a Gaussian-mass or covariance conclusion assumed in advance.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

def gaussianPositionEllipsoidMassExponent (c : ℝ) : ℝ :=
  1 / 8 - Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - Real.log c

theorem gaussianPosition_density_lower_on_ball (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hrsq : r ^ 2 ≤ (n : ℝ) / 4)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ closedBall 0 r) :
    Real.exp ((n : ℝ) * (Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - 1 / 8)) ≤
      standardGaussianDensity n x := by
  have hnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hp := mul_nonneg (sub_nonneg.mpr hnorm) (add_nonneg hr (norm_nonneg x))
  have hlog : (n : ℝ) * (Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - 1 / 8) ≤
      Real.log (standardGaussianDensity n x) := by
    rw [log_standardGaussianDensity]
    nlinarith
  exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (standardGaussianDensity_pos n x))

theorem gaussianPosition_gaussian_mass_lower_intersection (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (r : ℝ) (hr : 0 ≤ r) (hrsq : r ^ 2 ≤ (n : ℝ) / 4) :
    Real.exp ((n : ℝ) * (Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - 1 / 8)) *
      (volume (K ∩ closedBall 0 r)).toReal ≤
        (stdGaussian (EuclideanSpace ℝ (Fin n))).real K := by
  let I := K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  let L : ℝ := Real.exp ((n : ℝ) * (Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - 1 / 8))
  have hI : IsCompact I := hK.inter_right isClosed_closedBall
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => L) I :=
    ContinuousOn.integrableOn_compact hI continuousOn_const
  have hφ : IntegrableOn (standardGaussianDensity n) I :=
    (gaussianPosition_standardDensity_integrable n).restrict
  have hle : (∫ x in I, L) ≤ ∫ x in I, standardGaussianDensity n x := by
    exact setIntegral_mono_on hconst hφ hI.measurableSet
      (fun x hx => gaussianPosition_density_lower_on_ball n r hr hrsq x hx.2)
  have hmass : (stdGaussian (EuclideanSpace ℝ (Fin n))).real I =
      ∫ x in I, standardGaussianDensity n x := by
    have h := gaussianPosition_gaussian_set_integral n I hI.measurableSet (fun _ => (1 : ℝ))
    simpa only [one_mul, integral_const, measureReal_def, Measure.restrict_apply_univ,
      smul_eq_mul, mul_one] using h
  have hsub : (stdGaussian (EuclideanSpace ℝ (Fin n))).real I ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real K :=
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
      (measure_mono inter_subset_left)
  rw [integral_const] at hle
  simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul] at hle
  rw [mul_comm] at hle
  exact hle.trans (hmass.symm.le.trans hsub)

theorem gaussianPosition_mass_lower_of_ball_intersection (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (r : ℝ) (hr : 0 ≤ r) (hrsq : r ^ 2 ≤ (n : ℝ) / 4)
    (c : ℝ) (hc : 0 < c)
    (hinter : ENNReal.ofReal (c ^ n) ≤ volume (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r)) :
    Real.exp (-gaussianPositionEllipsoidMassExponent c * (n : ℝ)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real K := by
  have hI : IsCompact (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r) := hK.inter_right isClosed_closedBall
  have hvol : c ^ n ≤ (volume (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r)).toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hI.measure_lt_top.ne).mpr hinter
    simpa only [ENNReal.toReal_ofReal (pow_nonneg hc.le n)] using h
  have h := (mul_le_mul_of_nonneg_left hvol
    (le_of_lt (Real.exp_pos ((n : ℝ) * (Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - 1 / 8))))).trans
      (gaussianPosition_gaussian_mass_lower_intersection n K hK r hr hrsq)
  have heq : Real.exp ((n : ℝ) * (Real.log ((Real.sqrt (2 * Real.pi))⁻¹) - 1 / 8)) * c ^ n =
      Real.exp (-gaussianPositionEllipsoidMassExponent c * (n : ℝ)) := by
    rw [← Real.exp_log (pow_pos hc n), Real.log_pow, ← Real.exp_add]
    congr 1
    dsimp only [gaussianPositionEllipsoidMassExponent]
    ring
  rwa [heq] at h

end AffineFKProof
