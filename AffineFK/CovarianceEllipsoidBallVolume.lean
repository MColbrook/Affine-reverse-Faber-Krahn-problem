module

public import AffineFK.GaussianPositionMassCovariance

/-!
# A dimension-exponential volume bound for the covariance-radius ball

The explicit standard Gaussian density is bounded below on the ball of
radius sqrt(2n). Its genuine global integral equals one, giving the
volume estimate without Stirling's formula or a numerical oracle.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

def covarianceEllipsoidBallVolumeBase : ℝ :=
  Real.exp (1-Real.log ((Real.sqrt (2*Real.pi))⁻¹))

theorem covarianceEllipsoidBallVolumeBase_pos : 0 < covarianceEllipsoidBallVolumeBase :=
  Real.exp_pos _

theorem covarianceEllipsoid_ball_density_lower (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))) :
    Real.exp ((n : ℝ)*(Real.log ((Real.sqrt (2*Real.pi))⁻¹)-1)) ≤
      standardGaussianDensity n x := by
  have hnorm : ‖x‖ ≤ Real.sqrt (2*(n : ℝ)) := by
    simpa only [mem_closedBall,dist_zero_right] using hx
  have hsq := pow_le_pow_left₀ (norm_nonneg x) hnorm 2
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*(n : ℝ))] at hsq
  have hlog : (n : ℝ)*(Real.log ((Real.sqrt (2*Real.pi))⁻¹)-1) ≤
      Real.log (standardGaussianDensity n x) := by
    rw [log_standardGaussianDensity]
    nlinarith
  exact (Real.exp_le_exp.mpr hlog).trans_eq
    (Real.exp_log (standardGaussianDensity_pos n x))

theorem covarianceEllipsoid_ball_volume (n : ℕ) :
    (volume (closedBall (0 : EuclideanSpace ℝ (Fin n))
      (Real.sqrt (2*(n : ℝ))))).toReal ≤ covarianceEllipsoidBallVolumeBase^n := by
  let E := closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))
  let L := Real.exp ((n : ℝ)*(Real.log ((Real.sqrt (2*Real.pi))⁻¹)-1))
  have hE : IsCompact E := isCompact_closedBall _ _
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => L) E :=
    ContinuousOn.integrableOn_compact hE continuousOn_const
  have hphi : IntegrableOn (standardGaussianDensity n) E :=
    (gaussianPosition_standardDensity_integrable n).restrict
  have hlow : (∫ x in E, L) ≤ ∫ x in E, standardGaussianDensity n x :=
    setIntegral_mono_on hconst hphi hE.measurableSet
      (fun x hx => covarianceEllipsoid_ball_density_lower n x hx)
  have hupper : (∫ x in E, standardGaussianDensity n x) ≤ 1 := by
    rw [← gaussianPosition_standardDensity_integral n]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => (standardGaussianDensity_pos n x).le)
      (gaussianPosition_standardDensity_integrable n)
  have hmul : (volume E).toReal*L ≤ 1 := by
    simpa only [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul]
      using hlow.trans hupper
  have hL : 0 < L := Real.exp_pos _
  have hdiv : (volume E).toReal ≤ 1/L := (le_div_iff₀ hL).mpr hmul
  have hfactor : 1/L = covarianceEllipsoidBallVolumeBase^n := by
    dsimp only [L,covarianceEllipsoidBallVolumeBase]
    rw [one_div,← Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    ring
  exact hdiv.trans_eq hfactor

end AffineFKProof
