module

public import AffineFK.BridgeSchauderSeries
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The deterministic covariance kernel of the dyadic tents

This module is purely deterministic. The binary refinement identity will
identify its continuous geometric series with `min(s,t)-s*t` by a sup-norm
contraction, without assuming a Brownian bridge covariance formula.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeTent_zero_of_nonpos (j k : ℕ) (t : ℝ) (ht : t ≤ 0) : bridgeTent j k t = 0 := by
  have hp : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have hz : (2 : ℝ) ^ (j + 1) * t - (2 * (k : ℝ) + 1) ≤ 0 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  unfold bridgeTent
  rw [abs_of_nonpos hz]
  exact max_eq_left (by nlinarith [Nat.cast_nonneg (α := ℝ) k])

theorem bridgeTent_zero_of_one_le (j : ℕ) (k : Fin (2 ^ j)) (t : ℝ) (ht : 1 ≤ t) :
    bridgeTent j k t = 0 := by
  have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ j := by exact_mod_cast k.isLt
  have hp : 0 < (2 : ℝ) ^ (j + 1) := by positivity
  have heq : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
  have hz : 0 ≤ (2 : ℝ) ^ (j + 1) * t - (2 * (k : ℝ) + 1) := by rw [heq] at *; nlinarith
  unfold bridgeTent
  rw [abs_of_nonneg hz]
  exact max_eq_left (by rw [heq] at *; nlinarith)

theorem bridgeTent_left_scale (j k : ℕ) (t : ℝ) :
    bridgeTent (j + 1) k t = bridgeTent j k (2 * t) := by
  unfold bridgeTent
  rw [pow_succ]
  congr 3 <;> ring

theorem bridgeTent_right_scale (j k : ℕ) (t : ℝ) :
    bridgeTent (j + 1) (2 ^ j + k) t = bridgeTent j k (2 * t - 1) := by
  have heq : (2 : ℝ) ^ (j + 1 + 1) * t - (2 * ((2 ^ j + k : ℕ) : ℝ) + 1) =
      (2 : ℝ) ^ (j + 1) * (2 * t - 1) - (2 * (k : ℝ) + 1) := by
    push_cast
    rw [pow_succ, pow_succ]
    ring
  unfold bridgeTent
  rw [heq]

def bridgeLevelTentKernel (j : ℕ) (s t : ℝ) : ℝ :=
  ∑ k : Fin (2 ^ j), bridgeTent j k s * bridgeTent j k t

theorem bridgeLevelTentKernel_nonneg (j : ℕ) (s t : ℝ) : 0 ≤ bridgeLevelTentKernel j s t :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (bridgeTent_nonneg _ _ _) (bridgeTent_nonneg _ _ _))

theorem bridgeLevelTentKernel_le_one (j : ℕ) (s t : ℝ) : bridgeLevelTentKernel j s t ≤ 1 := by
  classical
  by_cases h : ∃ k : Fin (2 ^ j), bridgeTent j k s ≠ 0
  · obtain ⟨k, hk⟩ := h
    have hsum : bridgeLevelTentKernel j s t = bridgeTent j k s * bridgeTent j k t := by
      apply Finset.sum_eq_single k
      · intro l _ hl
        have hz : bridgeTent j l s = 0 := by
          by_contra hne
          exact hl (Fin.ext (bridgeTent_unique j l k s hne hk))
        simp [hz]
      · simp
    rw [hsum]
    exact (mul_le_of_le_one_left (bridgeTent_nonneg j k t) (bridgeTent_le_one j k s)).trans
      (bridgeTent_le_one j k t)
  · push_neg at h
    simp [bridgeLevelTentKernel, h]

theorem bridgeLevelTentKernel_continuous (j : ℕ) :
    Continuous (fun p : ℝ × ℝ => bridgeLevelTentKernel j p.1 p.2) := by
  unfold bridgeLevelTentKernel bridgeTent
  fun_prop

theorem bridgeLevelTentKernel_symm (j : ℕ) (s t : ℝ) :
    bridgeLevelTentKernel j s t = bridgeLevelTentKernel j t s := by
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem bridgeLevelTentKernel_zero_nonpos (j : ℕ) (s t : ℝ) (hs : s ≤ 0) :
    bridgeLevelTentKernel j s t = 0 := by
  simp [bridgeLevelTentKernel, bridgeTent_zero_of_nonpos j _ s hs]

theorem bridgeLevelTentKernel_zero_one_le (j : ℕ) (s t : ℝ) (hs : 1 ≤ s) :
    bridgeLevelTentKernel j s t = 0 := by
  unfold bridgeLevelTentKernel
  apply Finset.sum_eq_zero
  intro k _
  rw [bridgeTent_zero_of_one_le j k s hs, zero_mul]

theorem bridgeLevelTentKernel_refinement (j : ℕ) (s t : ℝ) :
    bridgeLevelTentKernel (j + 1) s t =
      bridgeLevelTentKernel j (2 * s) (2 * t) +
        bridgeLevelTentKernel j (2 * s - 1) (2 * t - 1) := by
  have hpow : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ, Nat.mul_two]
  unfold bridgeLevelTentKernel
  rw [hpow, Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    change bridgeTent (j + 1) (k : ℕ) s * bridgeTent (j + 1) (k : ℕ) t = _
    rw [bridgeTent_left_scale, bridgeTent_left_scale]
  · apply Finset.sum_congr rfl
    intro k _
    change bridgeTent (j + 1) (2 ^ j + (k : ℕ)) s *
      bridgeTent (j + 1) (2 ^ j + (k : ℕ)) t = _
    rw [bridgeTent_right_scale, bridgeTent_right_scale]

def bridgeTentCovarianceKernel (s t : ℝ) : ℝ :=
  ∑' j : ℕ, ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j) * bridgeLevelTentKernel j s t

theorem bridgeTentCovarianceKernel_summable (s t : ℝ) :
    Summable (fun j : ℕ => ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ j) * bridgeLevelTentKernel j s t) := by
  have hs := (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 / 2 : ℝ) < 1)).summable.mul_left (1 / 4 : ℝ)
  apply hs.of_nonneg_of_le
  · intro j
    exact mul_nonneg (by positivity) (bridgeLevelTentKernel_nonneg j s t)
  · intro j
    exact mul_le_of_le_one_right (by positivity) (bridgeLevelTentKernel_le_one j s t)

theorem bridgeTentCovarianceKernel_continuous :
    Continuous (fun p : ℝ × ℝ => bridgeTentCovarianceKernel p.1 p.2) := by
  unfold bridgeTentCovarianceKernel
  apply continuous_tsum
  · intro j
    exact continuous_const.mul (bridgeLevelTentKernel_continuous j)
  · exact (hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).summable.mul_left (1 / 4 : ℝ)
  · intro j p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (bridgeLevelTentKernel_nonneg j p.1 p.2))]
    exact mul_le_of_le_one_right (by positivity) (bridgeLevelTentKernel_le_one j p.1 p.2)

end AffineFKProof
