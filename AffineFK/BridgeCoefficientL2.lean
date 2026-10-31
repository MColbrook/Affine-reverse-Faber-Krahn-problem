module

public import AffineFK.BridgeSeriesAEConvergence
public import AffineFK.GaussianL2Limit
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Actual Gaussian coefficients and Schauder levels in L2

The finite-dimensional Gaussian laws and the coefficient normalization
are consequences of the actual countable product measure. The norm
bound at a fixed time uses one nonzero tent per level. No Gaussianity,
covariance or Brownian identification of the infinite path is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeCoefficient_isGaussianProcess (n : ℕ) :
    IsGaussianProcess (fun (p : Σ j : ℕ, Fin (2 ^ j))
      (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) => ω p.1 p.2)
      (bridgeCoefficientMeasure n) := by
  constructor
  intro I
  have hi := (bridgeCoefficientMeasure_independent n).precomp
    (show Function.Injective (fun p : I => p.1) from Subtype.val_injective)
  exact hi.hasGaussianLaw (fun p => (bridgeCoefficientMeasure_hasLaw n p.1.1 p.1.2).hasGaussianLaw)

theorem bridgeScalarCoefficient_gaussian (n j : ℕ) (k : Fin (2 ^ j)) (i : Fin n) :
    HasGaussianLaw
      (fun ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n) => ω j k i)
      (bridgeCoefficientMeasure n) := by
  simpa only [coordinateFunctional_apply] using
    (bridgeCoefficientMeasure_hasLaw n j k).hasGaussianLaw.map_fun (coordinateFunctional n i)

def bridgeScalarCoefficientL2 (n j : ℕ) (k : Fin (2 ^ j)) (i : Fin n) :
    Lp ℝ 2 (bridgeCoefficientMeasure n) :=
  (bridgeScalarCoefficient_gaussian n j k i).memLp_two.toLp (fun ω => ω j k i)

theorem bridgeScalarCoefficientL2_coe (n j : ℕ) (k : Fin (2 ^ j)) (i : Fin n) :
    (bridgeScalarCoefficientL2 n j k i :
      (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) → ℝ) =ᵐ[bridgeCoefficientMeasure n]
        (fun ω => ω j k i) := (bridgeScalarCoefficient_gaussian n j k i).memLp_two.coeFn_toLp

theorem bridgeGaussian_coordinate_second_moment (n : ℕ) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 1 := by
  have hmean := integral_strongDual_stdGaussian (coordinateFunctional n i)
  have hv := variance_dual_stdGaussian (coordinateFunctional n i)
  rw [variance_of_integral_eq_zero (coordinateFunctional n i).continuous.measurable.aemeasurable hmean] at hv
  simp only [coordinateFunctional_apply] at hv
  simpa [coordinateFunctional] using hv

theorem bridgeScalarCoefficientL2_norm (n j : ℕ) (k : Fin (2 ^ j)) (i : Fin n) :
    ‖bridgeScalarCoefficientL2 n j k i‖ = 1 := by
  have hsq : ‖bridgeScalarCoefficientL2 n j k i‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    calc
      _ = ∫ ω, (ω j k i) ^ 2 ∂bridgeCoefficientMeasure n := by
        apply integral_congr_ae
        filter_upwards [bridgeScalarCoefficientL2_coe n j k i] with ω hω
        simp [hω, pow_two]
      _ = ∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
        (bridgeCoefficientMeasure_hasLaw n j k).integral_comp
          (f := fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2) (by fun_prop)
      _ = 1 := bridgeGaussian_coordinate_second_moment n i
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)

theorem bridgeTent_sum_single_module {E : Type*} [AddCommGroup E] [Module ℝ E]
    (j : ℕ) (v : Fin (2 ^ j) → E) (t : ℝ) :
    (∑ k : Fin (2 ^ j), (bridgeTent j k t) • v k) = 0 ∨
      ∃ k : Fin (2 ^ j), (∑ l : Fin (2 ^ j), (bridgeTent j l t) • v l) =
        (bridgeTent j k t) • v k := by
  classical
  by_cases h : ∃ k : Fin (2 ^ j), bridgeTent j k t ≠ 0
  · obtain ⟨k, hk⟩ := h
    right
    refine ⟨k, Finset.sum_eq_single k ?_ (by simp)⟩
    intro l _ hl
    have hz : bridgeTent j l t = 0 := by
      by_contra hne
      exact hl (Fin.ext (bridgeTent_unique j l k t hne hk))
    simp [hz]
  · left
    push_neg at h
    simp [h]

def bridgeScalarLevelL2 (n : ℕ) (i : Fin n) (j : ℕ) (t : ℝ) :
    Lp ℝ 2 (bridgeCoefficientMeasure n) :=
  ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) •
    ∑ k : Fin (2 ^ j), (bridgeTent j k t) • bridgeScalarCoefficientL2 n j k i

theorem bridgeScalarLevelL2_norm_bound (n : ℕ) (i : Fin n) (j : ℕ) (t : ℝ) :
    ‖bridgeScalarLevelL2 n i j t‖ ≤ (2 : ℝ) ^ (-(j : ℝ) / 2 - 1) := by
  have hsum : ‖∑ k : Fin (2 ^ j), (bridgeTent j k t) • bridgeScalarCoefficientL2 n j k i‖ ≤ 1 := by
    rcases bridgeTent_sum_single_module j (fun k => bridgeScalarCoefficientL2 n j k i) t with
      hzero | ⟨k, hk⟩
    · simp [hzero]
    · rw [hk, norm_smul, Real.norm_eq_abs, abs_of_nonneg (bridgeTent_nonneg _ _ _),
        bridgeScalarCoefficientL2_norm, mul_one]
      exact bridgeTent_le_one _ _ _
  unfold bridgeScalarLevelL2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
  exact mul_le_of_le_one_right (by positivity) hsum

end AffineFKProof
