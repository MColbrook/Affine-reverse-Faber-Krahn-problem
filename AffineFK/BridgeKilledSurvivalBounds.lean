module

public import AffineFK.BridgeKilledDiagonalConvexity
public import Mathlib.Analysis.Convex.Basic

/-!
# Actual diagonal positivity and logarithmic bounds from bridge survival

For a convex domain containing zero, contraction of a surviving actual
bridge path still survives. A genuine lower bound at unit time therefore
bounds the selected killed diagonal at every positive time at most one.
The free Gaussian logarithmic ratio is computed with its exact normalization.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridgeFreeHeatDensity_pos (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin n)) : 0 < bridgeFreeHeatDensity n t x y := by
  unfold bridgeFreeHeatDensity
  exact mul_pos (inv_pos.mpr (pow_pos (Real.sqrt_pos.mpr ht) n))
    (standardGaussianDensity_pos n _)

theorem bridgeKilledKernel_lower_of_unit_survival (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hconv : Convex ℝ Ω) (hzero : 0 ∈ Ω)
    (B : ℝ) (hunit : ENNReal.ofReal (Real.exp (-B)) ≤
      bridgeSeriesLaw n (bridgeBrownianSurvivalSet n Ω))
    (t : ℝ) (ht : 0 < t) (htone : t ≤ 1) :
    ENNReal.ofReal (bridgeFreeHeatDensity n t 0 0 * Real.exp (-B)) ≤ bridgeKilledKernel n t 0 Ω 0 := by
  have hs : Real.sqrt t ≤ 1 := (Real.sqrt_le_one).mpr htone
  have hp : bridgeSeriesLaw n (bridgeBrownianSurvivalSet n Ω) ≤
      bridgeSeriesLaw n {f | ∀ u : Icc (0 : ℝ) 1, Real.sqrt t • f u ∈ Ω} := by
    apply measure_mono
    intro f hf u
    exact hconv.smul_mem_of_zero_mem hzero (hf u) ⟨Real.sqrt_nonneg _, hs⟩
  rw [bridgeKilledKernel_bridge_formula n t ht 0 0 Ω,
    ENNReal.ofReal_mul (bridgeFreeHeatDensity_pos n t ht 0 0).le]
  simp only [sub_self, smul_zero, add_zero, zero_add]
  exact mul_le_mul_right (hunit.trans hp) (ENNReal.ofReal (bridgeFreeHeatDensity n t 0 0))

theorem bridgeKilledDiagonal_pos_and_log_lower (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hconv : Convex ℝ Ω) (hzero : 0 ∈ Ω)
    (B : ℝ) (hunit : ENNReal.ofReal (Real.exp (-B)) ≤
      bridgeSeriesLaw n (bridgeBrownianSurvivalSet n Ω))
    (t : ℝ) (ht : 0 < t) (htone : t ≤ 1) :
    0 < bridgeKilledDiagonal n t 0 Ω ∧
      Real.log (bridgeFreeHeatDensity n t 0 0) - B ≤ Real.log (bridgeKilledDiagonal n t 0 Ω) := by
  have hf := bridgeFreeHeatDensity_pos n t ht 0 0
  have hlow := (ENNReal.ofReal_le_iff_le_toReal (bridgeKilledKernel_ne_top n t 0 0 Ω)).mp
    (bridgeKilledKernel_lower_of_unit_survival n Ω hconv hzero B hunit t ht htone)
  change bridgeFreeHeatDensity n t 0 0 * Real.exp (-B) ≤ bridgeKilledDiagonal n t 0 Ω at hlow
  have hp : 0 < bridgeKilledDiagonal n t 0 Ω :=
    (mul_pos hf (Real.exp_pos _)).trans_le hlow
  refine ⟨hp, ?_⟩
  have hl := Real.log_le_log (mul_pos hf (Real.exp_pos _)) hlow
  rw [Real.log_mul hf.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  linarith

theorem bridgeKilledDiagonal_log_upper (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hd : 0 < bridgeKilledDiagonal n t 0 Ω) :
    Real.log (bridgeKilledDiagonal n t 0 Ω) ≤ Real.log (bridgeFreeHeatDensity n t 0 0) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (bridgeKilledKernel_le_free n t 0 0 Ω)
  rw [ENNReal.toReal_ofReal (bridgeFreeHeatDensity_pos n t ht 0 0).le] at h
  exact Real.log_le_log hd h

theorem bridgeFreeHeatDensity_log_double_ratio (n : ℕ) (a : ℝ) (ha : 0 < a) :
    Real.log (bridgeFreeHeatDensity n a 0 0) - Real.log (bridgeFreeHeatDensity n (2*a) 0 0) =
      (n : ℝ)/2 * Real.log 2 := by
  rw [bridgeFreeHeatDensity_diagonal n a ha 0,
    bridgeFreeHeatDensity_diagonal n (2*a) (by positivity) 0,
    Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
  have he : 2*Real.pi*(2*a) = 2*(2*Real.pi*a) := by ring
  rw [he, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2*Real.pi*a ≠ 0)]
  ring

theorem bridgeKilledDiagonal_log_double_bound (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hconv : Convex ℝ Ω) (hzero : 0 ∈ Ω)
    (B : ℝ) (hunit : ENNReal.ofReal (Real.exp (-B)) ≤
      bridgeSeriesLaw n (bridgeBrownianSurvivalSet n Ω))
    (a : ℝ) (ha : 0 < a) (hatwo : 2*a ≤ 1) :
    Real.log (bridgeKilledDiagonal n a 0 Ω) - Real.log (bridgeKilledDiagonal n (2*a) 0 Ω) ≤
      B + (n : ℝ)/2 * Real.log 2 := by
  have hpa := bridgeKilledDiagonal_pos_and_log_lower n Ω hconv hzero B hunit a ha (by linarith)
  have hp2 := bridgeKilledDiagonal_pos_and_log_lower n Ω hconv hzero B hunit (2*a) (by positivity) hatwo
  have hu := bridgeKilledDiagonal_log_upper n a ha Ω hpa.1
  have hr := bridgeFreeHeatDensity_log_double_ratio n a ha
  linarith

end AffineFKProof
