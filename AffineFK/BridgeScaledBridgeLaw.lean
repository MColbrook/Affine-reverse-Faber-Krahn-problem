module

public import AffineFK.BridgeGaussianPathImage
public import AffineFK.BridgeStartedBrownian

/-!
# The actual centered bridge law on every positive finite horizon

This is the measurable image `sqrt(T) beta(t/T)` of the actual continuous
unit bridge. Its Gaussian law, centered means and exact bridge covariance
are proved from that image, without a conditional-law premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

/-- The actual centered Brownian bridge probability on `[0,T]`, obtained
by the measurable dilation `sqrt(T) beta(t/T)` of the constructed unit bridge. -/
def bridgeScaledBridgeLaw (n : ℕ) (T : ℝ) (hT : 0 < T) :
    Measure C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) :=
  (bridgeSeriesLaw n).map (bridgeScaledBrownianPath n T hT)

instance bridgeScaledBridgeLaw_probability (n : ℕ) (T : ℝ) (hT : 0 < T) :
    IsProbabilityMeasure (bridgeScaledBridgeLaw n T hT) :=
  (Measure.isProbabilityMeasure_map_iff (bridgeScaledBrownianPath_measurable n T hT).aemeasurable).mpr
    inferInstance

theorem bridgeScaledBridgeLaw_gaussian_process (n : ℕ) (T : ℝ) (hT : 0 < T) :
    IsGaussianProcess (fun q : Icc (0 : ℝ) T × Fin n =>
      fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f q.1 q.2)
      (bridgeScaledBridgeLaw n T hT) := by
  have hG := ((bridgeSeriesLaw_gaussian_process n).comp_right
    (fun q : Icc (0 : ℝ) T × Fin n => (bridgeUnitTime T hT q.1,q.2))).smul
      (fun _ : Icc (0 : ℝ) T × Fin n => Real.sqrt T)
  constructor
  intro I
  let F := fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => fun q : I => f q.1.1 q.1.2
  have hF : Measurable F := by fun_prop
  refine ⟨hF.aemeasurable, ?_⟩
  change IsGaussian ((bridgeScaledBridgeLaw n T hT).map F)
  rw [bridgeScaledBridgeLaw, Measure.map_map hF (bridgeScaledBrownianPath_measurable n T hT)]
  exact (hG.hasGaussianLaw I).isGaussian_map

theorem bridgeScaledBridgeLaw_coordinate_mean (n : ℕ) (T : ℝ) (hT : 0 < T)
    (r : Icc (0 : ℝ) T) (i : Fin n) :
    (∫ f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)), f r i ∂bridgeScaledBridgeLaw n T hT) = 0 := by
  have he : Measurable (fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f r i) :=
    (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp
      (ContinuousMap.measurable_eval r))
  rw [bridgeScaledBridgeLaw, integral_map (bridgeScaledBrownianPath_measurable n T hT).aemeasurable
    he.aestronglyMeasurable]
  change (∫ f, Real.sqrt T * f (bridgeUnitTime T hT r) i ∂bridgeSeriesLaw n) = 0
  rw [integral_const_mul, bridgeSeriesLaw_coordinate_mean, mul_zero]

theorem bridgeScaledBridgeLaw_coordinate_covariance (n : ℕ) (T : ℝ) (hT : 0 < T)
    (r u : Icc (0 : ℝ) T) (i j : Fin n) :
    cov[fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f r i,
      fun f => f u j; bridgeScaledBridgeLaw n T hT] =
      (min (r:ℝ) (u:ℝ)-(r:ℝ)*(u:ℝ)/T) * (if i=j then 1 else 0) := by
  have he (a : Icc (0 : ℝ) T) (l : Fin n) :
      Measurable (fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f a l) :=
    (measurable_pi_apply l).comp ((WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp
      (ContinuousMap.measurable_eval a))
  rw [bridgeScaledBridgeLaw, covariance_map (he r i).aestronglyMeasurable
    (he u j).aestronglyMeasurable (bridgeScaledBrownianPath_measurable n T hT).aemeasurable]
  change cov[fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
    Real.sqrt T * f (bridgeUnitTime T hT r) i,
    fun f => Real.sqrt T * f (bridgeUnitTime T hT u) j; bridgeSeriesLaw n] = _
  rw [covariance_const_mul_left, covariance_const_mul_right, bridgeSeriesLaw_brownian_covariance]
  change Real.sqrt T * (Real.sqrt T * ((min ((r:ℝ)/T) ((u:ℝ)/T) -
    ((r:ℝ)/T)*((u:ℝ)/T))*(if i=j then 1 else 0))) = _
  rw [min_div_div_right hT.le]
  calc
    _ = (Real.sqrt T * Real.sqrt T) *
      (min (r:ℝ) (u:ℝ)/T-((r:ℝ)/T)*((u:ℝ)/T)) * (if i=j then 1 else 0) := by ring
    _ = _ := by
      rw [Real.mul_self_sqrt hT.le]
      field_simp

end AffineFKProof
