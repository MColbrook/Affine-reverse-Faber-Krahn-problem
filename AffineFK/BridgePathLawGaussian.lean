module

public import AffineFK.BridgeGaussianProcess

/-!
# Gaussian laws and zero endpoints on the actual continuous-path carrier

The finite-dimensional Gaussian assertion is transported through the
genuinely measurable path map. The endpoint identities hold for every
coefficient array. The Brownian covariance is still a separate task.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeSeriesLaw_gaussian_process (n : ℕ) :
    IsGaussianProcess (fun p : Icc (0 : ℝ) 1 × Fin n =>
      (fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f p.1 p.2))
      (bridgeSeriesLaw n) := by
  constructor
  intro I
  have hG := (bridgeContinuousSeries_gaussian_process n).hasGaussianLaw I
  let g : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) → I → ℝ :=
    fun f q => f q.1.1 q.1.2
  have hg : Measurable g := by fun_prop
  refine ⟨hg.aemeasurable, ?_⟩
  have heq : (bridgeSeriesLaw n).map g =
      (bridgeCoefficientMeasure n).map
        (fun ω => fun q : I => bridgeContinuousSeries n ω q.1.1 q.1.2) := by
    rw [bridgeSeriesLaw, Measure.map_map hg (bridgeContinuousSeries_measurable n)]
    rfl
  change IsGaussian ((bridgeSeriesLaw n).map g)
  rw [heq]
  exact hG.isGaussian_map

theorem bridgeTent_zero (j k : ℕ) : bridgeTent j k 0 = 0 := by
  unfold bridgeTent
  simp only [mul_zero, zero_sub, abs_neg]
  rw [abs_of_nonneg (by positivity)]
  exact max_eq_left (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

theorem bridgeTent_one (j : ℕ) (k : Fin (2 ^ j)) : bridgeTent j k 1 = 0 := by
  have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
    exact_mod_cast k.isLt
  have heq : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
  have hpos : 0 ≤ (2 : ℝ) ^ (j + 1) - (2 * (k : ℝ) + 1) := by rw [heq]; linarith
  unfold bridgeTent
  rw [mul_one, abs_of_nonneg hpos, heq]
  exact max_eq_left (by linarith)

theorem bridgeContinuousSeries_zero (n : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) :
    bridgeContinuousSeries n ω ⟨0, by norm_num⟩ = 0 := by
  by_cases h : Summable (fun j => bridgeSchauderLevelMap n j ω)
  · have heval := (ContinuousMap.evalCLM ℝ (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1)).map_tsum h
    simpa [bridgeContinuousSeries, bridgeSchauderLevelMap, bridgeSchauderLevel, bridgeTent_zero] using heval
  · simp [bridgeContinuousSeries, tsum_eq_zero_of_not_summable h]

theorem bridgeContinuousSeries_one (n : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) :
    bridgeContinuousSeries n ω ⟨1, by norm_num⟩ = 0 := by
  by_cases h : Summable (fun j => bridgeSchauderLevelMap n j ω)
  · have heval := (ContinuousMap.evalCLM ℝ (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)).map_tsum h
    simpa [bridgeContinuousSeries, bridgeSchauderLevelMap, bridgeSchauderLevel, bridgeTent_one] using heval
  · simp [bridgeContinuousSeries, tsum_eq_zero_of_not_summable h]

end AffineFKProof
