module

public import AffineFK.BridgeGaussianPathImage
public import AffineFK.BridgeBrownianCovariance

/-!
# Time reversal of the actual continuous Gaussian bridge law

Its centered Gaussian finite-dimensional laws have the already proved
covariance `min(s,t)-s*t`; the exact reversal identity for that covariance
and genuine continuous-path law uniqueness prove invariance of the law.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

def bridgeReverseUnitTime (u : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨1-u, sub_nonneg.mpr u.2.2, sub_le_self 1 u.2.1⟩

theorem bridgeReverseUnitTime_involutive : Function.Involutive bridgeReverseUnitTime := by
  intro u
  apply Subtype.ext
  change 1-(1-(u:ℝ)) = u
  ring

def bridgeReversePath (n : ℕ) (f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :
    C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) where
  toFun u := f (bridgeReverseUnitTime u)
  continuous_toFun := f.continuous.comp
    ((continuous_const.sub continuous_subtype_val).subtype_mk _)

theorem bridgeReversePath_measurable (n : ℕ) : Measurable (bridgeReversePath n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro u
  exact ContinuousMap.measurable_eval (bridgeReverseUnitTime u)

theorem bridge_covariance_time_reversal (s t : ℝ) :
    min (1-s) (1-t) - (1-s)*(1-t) = min s t - s*t := by
  by_cases h : s ≤ t
  · rw [min_eq_right (by linarith), min_eq_left h]
    ring
  · have h' : t ≤ s := (le_of_not_ge h)
    rw [min_eq_left (by linarith), min_eq_right h']
    ring

theorem bridgeSeriesLaw_reverse_hasLaw (n : ℕ) :
    HasLaw (bridgeReversePath n) (bridgeSeriesLaw n) (bridgeSeriesLaw n) := by
  refine ⟨(bridgeReversePath_measurable n).aemeasurable, ?_⟩
  apply bridge_gaussian_continuous_image_law_ext n (bridgeSeriesLaw n) (bridgeReversePath n)
    (bridgeReversePath_measurable n) (bridgeSeriesLaw n)
    ((bridgeSeriesLaw_gaussian_process n).comp_right
      (fun q : Icc (0 : ℝ) 1 × Fin n => (bridgeReverseUnitTime q.1,q.2)))
    (bridgeSeriesLaw_gaussian_process n)
  · intro t i
    exact (bridgeSeriesLaw_coordinate_mean n i _).trans (bridgeSeriesLaw_coordinate_mean n i t).symm
  · intro s t i j
    change cov[fun f => f (bridgeReverseUnitTime s) i,
      fun f => f (bridgeReverseUnitTime t) j; bridgeSeriesLaw n] = _
    rw [bridgeSeriesLaw_brownian_covariance, bridgeSeriesLaw_brownian_covariance]
    change (min (1-(s:ℝ)) (1-(t:ℝ)) - (1-(s:ℝ))*(1-(t:ℝ))) * _ = _
    rw [bridge_covariance_time_reversal]

end AffineFKProof
