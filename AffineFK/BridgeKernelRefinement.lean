module

public import AffineFK.BridgeTentKernel

/-!
# Exact binary refinement of the continuous tent covariance

All identities concern the actual summable deterministic kernel. They
follow from the two dyadic halves and carry the exact factor one half.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeTentCovarianceKernel_symm (s t : ℝ) :
    bridgeTentCovarianceKernel s t = bridgeTentCovarianceKernel t s := by
  apply tsum_congr
  intro j
  rw [bridgeLevelTentKernel_symm j s t]

theorem bridgeTentCovarianceKernel_zero_nonpos (s t : ℝ) (hs : s ≤ 0) :
    bridgeTentCovarianceKernel s t = 0 := by
  simp [bridgeTentCovarianceKernel, bridgeLevelTentKernel_zero_nonpos _ s t hs]

theorem bridgeTentCovarianceKernel_zero_one_le (s t : ℝ) (hs : 1 ≤ s) :
    bridgeTentCovarianceKernel s t = 0 := by
  simp [bridgeTentCovarianceKernel, bridgeLevelTentKernel_zero_one_le _ s t hs]

theorem bridgeTentCovarianceKernel_refinement (s t : ℝ) :
    bridgeTentCovarianceKernel s t =
      (1 / 4 : ℝ) * bridgeTent 0 0 s * bridgeTent 0 0 t +
        (1 / 2 : ℝ) * bridgeTentCovarianceKernel (2 * s) (2 * t) +
          (1 / 2 : ℝ) * bridgeTentCovarianceKernel (2 * s - 1) (2 * t - 1) := by
  have hs := bridgeTentCovarianceKernel_summable s t
  have hl := bridgeTentCovarianceKernel_summable (2 * s) (2 * t)
  have hr := bridgeTentCovarianceKernel_summable (2 * s - 1) (2 * t - 1)
  calc
    _ = (1 / 4 : ℝ) * bridgeLevelTentKernel 0 s t +
        ∑' j : ℕ, ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (j + 1)) * bridgeLevelTentKernel (j + 1) s t := by
      simpa only [bridgeTentCovarianceKernel, pow_zero, mul_one] using hs.tsum_eq_zero_add
    _ = (1 / 4 : ℝ) * bridgeLevelTentKernel 0 s t +
        ∑' j : ℕ, ((1 / 2 : ℝ) * (((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j) *
          bridgeLevelTentKernel j (2 * s) (2 * t)) +
          (1 / 2 : ℝ) * (((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j) *
            bridgeLevelTentKernel j (2 * s - 1) (2 * t - 1))) := by
      congr 1
      apply tsum_congr
      intro j
      rw [bridgeLevelTentKernel_refinement, pow_succ]
      ring
    _ = _ := by
      rw [(hl.mul_left (1 / 2 : ℝ)).tsum_add (hr.mul_left (1 / 2 : ℝ)),
        tsum_mul_left, tsum_mul_left]
      have hzero : bridgeLevelTentKernel 0 s t = bridgeTent 0 0 s * bridgeTent 0 0 t := by
        simp [bridgeLevelTentKernel]
      rw [hzero]
      change _ = (1 / 4 : ℝ) * bridgeTent 0 0 s * bridgeTent 0 0 t +
        (1 / 2 : ℝ) * (∑' j : ℕ, ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j) *
          bridgeLevelTentKernel j (2 * s) (2 * t)) +
        (1 / 2 : ℝ) * (∑' j : ℕ, ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j) *
          bridgeLevelTentKernel j (2 * s - 1) (2 * t - 1))
      ring

theorem bridgeTent_base_left (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    bridgeTent 0 0 t = 2 * t := by
  unfold bridgeTent
  norm_num only [Nat.zero_add, pow_one, Nat.cast_zero, mul_zero, zero_add]
  rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
  ring

theorem bridgeTent_base_right (t : ℝ) (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    bridgeTent 0 0 t = 2 * (1 - t) := by
  unfold bridgeTent
  norm_num only [Nat.zero_add, pow_one, Nat.cast_zero, mul_zero, zero_add]
  rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  ring

theorem bridgeTentCovarianceKernel_left (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    bridgeTentCovarianceKernel s t = s * t +
      (1 / 2 : ℝ) * bridgeTentCovarianceKernel (2 * s) (2 * t) := by
  rw [bridgeTentCovarianceKernel_refinement, bridgeTent_base_left s hs0 hs1,
    bridgeTent_base_left t ht0 ht1,
    bridgeTentCovarianceKernel_zero_nonpos (2 * s - 1) (2 * t - 1) (by linarith)]
  ring

theorem bridgeTentCovarianceKernel_right (s t : ℝ)
    (hs0 : 1 / 2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    bridgeTentCovarianceKernel s t = (1 - s) * (1 - t) +
      (1 / 2 : ℝ) * bridgeTentCovarianceKernel (2 * s - 1) (2 * t - 1) := by
  rw [bridgeTentCovarianceKernel_refinement, bridgeTent_base_right s hs0 hs1,
    bridgeTent_base_right t ht0 ht1,
    bridgeTentCovarianceKernel_zero_one_le (2 * s) (2 * t) (by linarith)]
  ring

theorem bridgeTentCovarianceKernel_cross (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    bridgeTentCovarianceKernel s t = s * (1 - t) := by
  have hl : bridgeTentCovarianceKernel (2 * s) (2 * t) = 0 := by
    rw [bridgeTentCovarianceKernel_symm]
    exact bridgeTentCovarianceKernel_zero_one_le _ _ (by linarith)
  rw [bridgeTentCovarianceKernel_refinement, bridgeTent_base_left s hs0 hs1,
    bridgeTent_base_right t ht0 ht1, hl,
    bridgeTentCovarianceKernel_zero_nonpos (2 * s - 1) (2 * t - 1) (by linarith)]
  ring

end AffineFKProof
