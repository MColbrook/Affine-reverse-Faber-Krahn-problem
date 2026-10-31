module

public import AffineFK.BridgeSeriesAlmostSure

/-!
# Almost-sure Banach-space convergence of the literal bridge series

The actual standard-Gaussian coefficient law supplies the summable bad-event
bound. Borel–Cantelli then yields a geometric eventual level bound and
genuine norm summability in continuous path space. No Brownian law,
desired covariance, convergence or finite entropy is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology

theorem bridgeCoefficient_ae_eventually_bound (n : ℕ) :
    ∀ᵐ ω ∂bridgeCoefficientMeasure n,
      ∀ᶠ j : ℕ in atTop, ∀ k : Fin (2 ^ j), ‖ω j k‖ ≤ (2 : ℝ) ^ ((j : ℝ) / 4) := by
  filter_upwards [ae_eventually_notMem (bridgeLevelMomentBad_summable_measure n)] with ω hω
  filter_upwards [hω] with j hj k
  have hnot : ¬ ENNReal.ofReal ((2 : ℝ) ^ (2 * j)) ≤ (ENNReal.ofReal ‖ω j k‖) ^ 8 := by
    intro h
    exact hj (mem_iUnion.mpr ⟨k, h⟩)
  have hp := lt_of_not_ge hnot
  rw [← ENNReal.ofReal_pow (norm_nonneg _) 8] at hp
  have hreal : ‖ω j k‖ ^ 8 < (2 : ℝ) ^ (2 * j) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hp
  have hrpow : ((2 : ℝ) ^ ((j : ℝ) / 4)) ^ 8 = (2 : ℝ) ^ (2 * j) := by
    rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num only [Nat.cast_ofNat]
    rw [show ((j : ℝ) / 4) * (8 : ℝ) = ((2 * j : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast _ _
  by_contra h
  have hle : ((2 : ℝ) ^ ((j : ℝ) / 4)) ^ 8 ≤ ‖ω j k‖ ^ 8 := by
    have : (2 : ℝ) ^ ((j : ℝ) / 4) ≤ ‖ω j k‖ := (lt_of_not_ge h).le
    gcongr
  rw [hrpow] at hle
  linarith

theorem bridgeSchauderLevel_norm_of_coefficient_bound (n j : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ k : Fin (2 ^ j), ‖ω j k‖ ≤ C) (t : ℝ) :
    ‖bridgeSchauderLevel n j ω t‖ ≤ ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) * C := by
  have hweight : 0 ≤ (2 : ℝ) ^ (-(j : ℝ) / 2 - 1) := by positivity
  have hsum : ‖∑ k : Fin (2 ^ j), (bridgeTent j k t) • ω j k‖ ≤ C := by
    rcases bridgeTent_sum_single n j ω t with hzero | ⟨k, hk⟩
    · simpa only [hzero, norm_zero] using hC
    · rw [hk, norm_smul, Real.norm_eq_abs, abs_of_nonneg (bridgeTent_nonneg _ _ _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (bridgeTent_le_one _ _ _)).trans (hbound k)
  unfold bridgeSchauderLevel
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hweight]
  exact mul_le_mul_of_nonneg_left hsum hweight

theorem bridgeSchauderLevel_quarter_bound (n j : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n))
    (hbound : ∀ k : Fin (2 ^ j), ‖ω j k‖ ≤ (2 : ℝ) ^ ((j : ℝ) / 4)) (t : ℝ) :
    ‖bridgeSchauderLevel n j ω t‖ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ ((-1 / 4 : ℝ) * (j : ℝ)) := by
  apply (bridgeSchauderLevel_norm_of_coefficient_bound n j ω _ (by positivity) hbound t).trans_eq
  have h := bridgeSchauder_weight_identity (1 / 4 : ℝ) j
  rw [show (1 / 4 : ℝ) * (j : ℝ) = (j : ℝ) / 4 by ring] at h
  norm_num at h
  simpa only [neg_mul, neg_div] using h

/-- The literal series converges in the norm of continuous path space almost surely. -/
theorem bridgeContinuousSeries_ae_summable (n : ℕ) :
    ∀ᵐ ω ∂bridgeCoefficientMeasure n, Summable (fun j => bridgeSchauderLevelMap n j ω) := by
  filter_upwards [bridgeCoefficient_ae_eventually_bound n] with ω hω
  have hs := (two_rpow_multiple_hasSum (-1 / 4 : ℝ) (by norm_num)).summable.mul_left (1 / 2 : ℝ)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hω] with j hj
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  exact bridgeSchauderLevel_quarter_bound n j ω hj t

/-- On one full-measure event the continuous path equals the actual pointwise
series at every time, with no exceptional set depending on time. -/
theorem bridgeContinuousSeries_ae_eq_pointwise (n : ℕ) :
    ∀ᵐ ω ∂bridgeCoefficientMeasure n, ∀ t : Icc (0 : ℝ) 1,
      bridgeContinuousSeries n ω t = bridgeSchauderSeries n ω t := by
  filter_upwards [bridgeContinuousSeries_ae_summable n] with ω hω t
  exact (ContinuousMap.evalCLM ℝ t).map_tsum hω

end AffineFKProof
