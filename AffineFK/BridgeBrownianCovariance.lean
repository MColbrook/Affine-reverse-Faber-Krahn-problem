module

public import AffineFK.BridgeKernelMinimum
public import AffineFK.BridgeSeriesCovariance
public import AffineFK.BridgePathLawGaussian

/-!
# The exact covariance of the constructed continuous Gaussian bridge

The actual independent-coefficient law has centred, jointly Gaussian
space-time evaluations and covariance `(min(s,t)-s*t) δᵢⱼ`.  The variance
normalisation is the standard one for Brownian motion with generator
one half of the Laplacian. No killed transition kernel is introduced here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeSchauder_weight_squared (j : ℕ) :
    ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) ^ 2 = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j := by
  rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))]
  norm_num only [Nat.cast_ofNat]
  rw [show (-(j : ℝ) / 2 - 1) * 2 = -(j : ℝ) + (-2) by ring,
    Real.rpow_add (by norm_num : 0 < (2 : ℝ)),
    Real.rpow_neg_eq_inv_rpow (2 : ℝ) (j : ℝ), Real.rpow_natCast]
  norm_num
  ring

theorem bridgeSeriesCovarianceKernel_eq_min (s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    bridgeSeriesCovarianceKernel s t = min s t - s * t := by
  calc
    _ = bridgeTentCovarianceKernel s t := by
      unfold bridgeSeriesCovarianceKernel bridgeTentCovarianceKernel
      apply tsum_congr
      intro j
      rw [bridgeSchauder_weight_squared]
      rfl
    _ = _ := bridgeTentCovarianceKernel_eq_min s t hs ht

theorem bridgeContinuousSeries_brownian_covariance (n : ℕ) (i l : Fin n)
    (s t : Icc (0 : ℝ) 1) :
    cov[fun ω => bridgeContinuousSeries n ω s i,
      fun ω => bridgeContinuousSeries n ω t l; bridgeCoefficientMeasure n] =
        (min (s : ℝ) t - (s : ℝ) * t) * (if i = l then 1 else 0) := by
  rw [bridgeContinuousSeries_coordinate_covariance,
    bridgeSeriesCovarianceKernel_eq_min s t s.property t.property]

theorem bridgeSeriesLaw_coordinate_mean (n : ℕ) (i : Fin n) (t : Icc (0 : ℝ) 1) :
    (∫ f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)), f t i
      ∂bridgeSeriesLaw n) = 0 := by
  have hm : Measurable (fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f t i) := by
    simpa only [Function.comp_def, coordinateFunctional_apply] using
      (coordinateFunctional n i).continuous.measurable.comp (ContinuousMap.measurable_eval t)
  rw [bridgeSeriesLaw, integral_map (bridgeContinuousSeries_measurable n).aemeasurable
    hm.aestronglyMeasurable]
  exact bridgeContinuousSeries_coordinate_mean n i t

theorem bridgeSeriesLaw_brownian_covariance (n : ℕ) (i l : Fin n)
    (s t : Icc (0 : ℝ) 1) :
    cov[fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f s i,
      fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f t l; bridgeSeriesLaw n] =
        (min (s : ℝ) t - (s : ℝ) * t) * (if i = l then 1 else 0) := by
  have hm (q : Icc (0 : ℝ) 1) (k : Fin n) :
      Measurable (fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f q k) := by
    simpa only [Function.comp_def, coordinateFunctional_apply] using
      (coordinateFunctional n k).continuous.measurable.comp (ContinuousMap.measurable_eval q)
  rw [bridgeSeriesLaw, covariance_map (hm s i).aestronglyMeasurable (hm t l).aestronglyMeasurable
    (bridgeContinuousSeries_measurable n).aemeasurable]
  exact bridgeContinuousSeries_brownian_covariance n i l s t

end AffineFKProof
