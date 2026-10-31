module

public import AffineFK.OUScoreInformationBounds
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Actual uniform positive-time score control for entropy dissipation

This reuses the proved conditional first-order OU contraction and actual
score identification. The initial input is a genuine L2 weak relative
score, not a desired entropy or dissipation bound. The resulting bound is
uniform over all positive times and concerns the actual density law.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem ou_entropy_initial_first_moment (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x) ν :=
  (memLp_piLp_iff.mpr hxi).integrable (by norm_num)

theorem ou_entropy_actual_score_uniform_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (t : ℝ) (ht : 0 < t) :
    let μ := densityMeasure n (gaussianSmoothingDensity n ν (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t))))
    let score := gaussianSmoothingScore n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    IsProbabilityMeasure μ ∧ MemLp score 2 μ ∧
      (∫ x, ‖score x‖ ^ 2 ∂μ) ≤ ∫ x, ‖v x‖ ^ 2 ∂ν := by
  have h := OU_firstOrder_relative_score_information_bound n ν hxi v hv hweak t ht
  have hlaw := gaussianSmoothingDensity_law n ν (Real.exp (-t))
    (Real.sqrt (1 - Real.exp (-2 * t))) (ou_smoothing_scale_domain t ht).2.1
  rw [hlaw] at h
  refine ⟨?_, h.1, h.2.trans ?_⟩
  · rw [← hlaw]
    infer_instance
  · have he : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he
      (integral_nonneg (fun x => sq_nonneg ‖v x‖))

end AffineFKProof
