module

public import AffineFK.BridgeKernelRefinement

/-!
# The exact Brownian bridge covariance

Binary refinement determines the continuous tent kernel uniquely on the
unit square.  The difference from `min(s,t)-s*t` contracts by one half
on either dyadic subsquare and vanishes on the two other rectangles.
The compact sup norm therefore forces the difference to vanish.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

def bridgeCovarianceDifference (s t : ℝ) : ℝ :=
  bridgeTentCovarianceKernel s t - (min s t - s * t)

theorem bridgeCovarianceDifference_symm (s t : ℝ) :
    bridgeCovarianceDifference s t = bridgeCovarianceDifference t s := by
  simp only [bridgeCovarianceDifference, bridgeTentCovarianceKernel_symm s t,
    min_comm s t, mul_comm s t]

theorem bridgeCovarianceDifference_left (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    bridgeCovarianceDifference s t =
      (1 / 2 : ℝ) * bridgeCovarianceDifference (2 * s) (2 * t) := by
  rw [bridgeCovarianceDifference, bridgeTentCovarianceKernel_left s t hs0 hs1 ht0 ht1]
  unfold bridgeCovarianceDifference
  by_cases hst : s ≤ t
  · rw [min_eq_left hst, min_eq_left (by linarith : 2 * s ≤ 2 * t)]
    ring
  · rw [min_eq_right (le_of_not_ge hst), min_eq_right (by linarith : 2 * t ≤ 2 * s)]
    ring

theorem bridgeCovarianceDifference_right (s t : ℝ)
    (hs0 : 1 / 2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    bridgeCovarianceDifference s t =
      (1 / 2 : ℝ) * bridgeCovarianceDifference (2 * s - 1) (2 * t - 1) := by
  rw [bridgeCovarianceDifference, bridgeTentCovarianceKernel_right s t hs0 hs1 ht0 ht1]
  unfold bridgeCovarianceDifference
  by_cases hst : s ≤ t
  · rw [min_eq_left hst, min_eq_left (by linarith : 2 * s - 1 ≤ 2 * t - 1)]
    ring
  · rw [min_eq_right (le_of_not_ge hst), min_eq_right (by linarith : 2 * t - 1 ≤ 2 * s - 1)]
    ring

theorem bridgeCovarianceDifference_cross (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    bridgeCovarianceDifference s t = 0 := by
  rw [bridgeCovarianceDifference, bridgeTentCovarianceKernel_cross s t hs0 hs1 ht0 ht1,
    min_eq_left (by linarith : s ≤ t)]
  ring

def bridgeCovarianceDifferenceMap : C((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1), ℝ) where
  toFun p := bridgeCovarianceDifference p.1 p.2
  continuous_toFun := by
    unfold bridgeCovarianceDifference
    exact (bridgeTentCovarianceKernel_continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).sub
      (((continuous_subtype_val.comp continuous_fst).min
        (continuous_subtype_val.comp continuous_snd)).sub
        ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_subtype_val.comp continuous_snd)))

theorem bridgeCovarianceDifferenceMap_bound (p : (Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) :
    ‖bridgeCovarianceDifferenceMap p‖ ≤ (1 / 2 : ℝ) * ‖bridgeCovarianceDifferenceMap‖ := by
  change ‖bridgeCovarianceDifference p.1 p.2‖ ≤ _
  by_cases hs : (p.1 : ℝ) ≤ 1 / 2
  · by_cases ht : (p.2 : ℝ) ≤ 1 / 2
    · let q : (Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1) :=
        (⟨2 * p.1, by constructor <;> nlinarith [p.1.property.1]⟩,
          ⟨2 * p.2, by constructor <;> nlinarith [p.2.property.1]⟩)
      rw [bridgeCovarianceDifference_left p.1 p.2 p.1.property.1 hs p.2.property.1 ht,
        norm_mul]
      rw [show ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) by norm_num]
      exact mul_le_mul_of_nonneg_left (bridgeCovarianceDifferenceMap.norm_coe_le_norm q)
        (by norm_num)
    · rw [bridgeCovarianceDifference_cross p.1 p.2 p.1.property.1 hs (by linarith)
        p.2.property.2, norm_zero]
      positivity
  · by_cases ht : (p.2 : ℝ) ≤ 1 / 2
    · rw [bridgeCovarianceDifference_symm, bridgeCovarianceDifference_cross p.2 p.1
        p.2.property.1 ht (by linarith) p.1.property.2, norm_zero]
      positivity
    · let q : (Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1) :=
        (⟨2 * p.1 - 1, by constructor <;> nlinarith [p.1.property.2]⟩,
          ⟨2 * p.2 - 1, by constructor <;> nlinarith [p.2.property.2]⟩)
      rw [bridgeCovarianceDifference_right p.1 p.2 (by linarith) p.1.property.2
        (by linarith) p.2.property.2, norm_mul]
      rw [show ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) by norm_num]
      exact mul_le_mul_of_nonneg_left (bridgeCovarianceDifferenceMap.norm_coe_le_norm q)
        (by norm_num)

theorem bridgeCovarianceDifferenceMap_eq_zero : bridgeCovarianceDifferenceMap = 0 := by
  have hbound : ‖bridgeCovarianceDifferenceMap‖ ≤
      (1 / 2 : ℝ) * ‖bridgeCovarianceDifferenceMap‖ :=
    (ContinuousMap.norm_le _ (by positivity)).mpr bridgeCovarianceDifferenceMap_bound
  apply norm_eq_zero.mp
  linarith [norm_nonneg bridgeCovarianceDifferenceMap]

theorem bridgeTentCovarianceKernel_eq_min (s t : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    bridgeTentCovarianceKernel s t = min s t - s * t := by
  have h := congrArg (fun f : C((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1), ℝ) =>
    f (⟨s, hs⟩, ⟨t, ht⟩)) bridgeCovarianceDifferenceMap_eq_zero
  change bridgeTentCovarianceKernel s t - (min s t - s * t) = 0 at h
  exact sub_eq_zero.mp h

end AffineFKProof
