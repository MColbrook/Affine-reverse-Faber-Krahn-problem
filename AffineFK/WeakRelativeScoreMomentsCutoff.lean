module

public import AffineFK.SobolevFisherIntegration

/-!
# Compact cutoff limits for weak relative score moments

Mixed coordinate/partial terms are bounded by the fixed cutoff-gradient
constant. Both derivative limits below are actual dominated-convergence
arguments on a probability space; no moment assumption is needed for the
boundary terms. The underlying smooth cutoffs and genuine product rule
are reused from the earlier project Sobolev construction.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

theorem weakRelativeScore_mixed_coordinate_partial_bound (n : ℕ) (i j : Fin n)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (houter : ∀ x, 2 ≤ ‖x‖ → χ x = 0)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x j * partialTest n i (cutoffSequence χ k) x‖ ≤ 2 * M := by
  let z := ((k : ℝ) + 1)⁻¹ • x
  have heq : x j * partialTest n i (cutoffSequence χ k) x = z j * partialTest n i χ z := by
    rw [sobolevFisher_scaled_partial]
    change x j * (_ * _) = (_ * x j) * _
    ring
  rw [heq]
  by_cases hz : ‖z‖ ≤ 2
  · have hp : ‖partialTest n i χ z‖ ≤ M := by
      rw [partialTest_apply]
      exact (PiLp.norm_apply_le (gradient χ z) i).trans (hM z)
    rw [norm_mul]
    exact (mul_le_mul (PiLp.norm_apply_le z j) hp (norm_nonneg _) (norm_nonneg z)).trans
      (mul_le_mul_of_nonneg_right hz hM0)
  · rw [partialTest_apply, sobolevFisher_cutoff_gradient_zero n χ houter z (lt_of_not_ge hz)]
    simp only [PiLp.zero_apply, mul_zero, norm_zero]
    positivity

theorem weakRelativeScore_coordinateCutoff_partial (n : ℕ) (i j : Fin n)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n i (coordinateCutoff n j χ k) x =
      (if i = j then (1 : ℝ) else 0) * cutoffSequence χ k x +
        x j * partialTest n i (cutoffSequence χ k) x := by
  rw [partialTest_apply, coordinateCutoff_gradient]
  by_cases hij : i = j
  · subst j
    simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.basisFun_apply,
      smul_eq_mul, partialTest_apply]
  · simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.basisFun_apply,
      smul_eq_mul, partialTest_apply, hij]

theorem weakRelativeScore_cutoff_derivative_integral_tendsto (n : ℕ) (i : Fin n)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M) :
    Tendsto (fun k => ∫ x, partialTest n i (cutoffSequence χ k) x ∂ν)
      atTop (𝓝 (0 : ℝ)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun k x => partialTest n i (cutoffSequence χ k) x)
    (f := fun _ => (0 : ℝ)) (fun _ => M)
    (fun k => (partialTest n i (cutoffSequence χ k)).continuous.aestronglyMeasurable)
    (integrable_const M)
    (fun k => Eventually.of_forall fun x => by
      rw [partialTest_apply]
      have hr : 0 < (k : ℝ) + 1 := by positivity
      have hd : M / ((k : ℝ) + 1) ≤ M := by
        apply (div_le_iff₀ hr).mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      exact (PiLp.norm_apply_le (gradient (cutoffSequence χ k) x) i).trans
        ((gradient_scaledTestFunction_bound _ hr χ M hM x).trans hd))
    (Eventually.of_forall fun x => (sobolevFisher_cutoff_pointwise n i χ hχ0 M hM x).2)
  simpa only [integral_zero] using h

theorem weakRelativeScore_coordinateCutoff_derivative_integral_tendsto
    (n : ℕ) (i j : Fin n)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (houter : ∀ x, 2 ≤ ‖x‖ → χ x = 0)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M) :
    Tendsto (fun k => ∫ x, partialTest n i (coordinateCutoff n j χ k) x ∂ν)
      atTop (𝓝 (if i = j then (1 : ℝ) else 0)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun k x => partialTest n i (coordinateCutoff n j χ k) x)
    (f := fun _ => if i = j then (1 : ℝ) else 0) (fun _ => 1 + 2 * M)
    (fun k => (partialTest n i (coordinateCutoff n j χ k)).continuous.aestronglyMeasurable)
    (integrable_const (1 + 2 * M))
    (fun k => Eventually.of_forall fun x => by
      rw [weakRelativeScore_coordinateCutoff_partial]
      have hc : ‖cutoffSequence χ k x‖ ≤ 1 := by
        rw [cutoffSequence_apply, Real.norm_eq_abs, abs_of_nonneg (hχ _).1]
        exact (hχ _).2
      have ha : ‖(if i = j then (1 : ℝ) else 0) * cutoffSequence χ k x‖ ≤ 1 := by
        split_ifs <;> simpa using hc
      exact (norm_add_le _ _).trans (add_le_add ha
        (weakRelativeScore_mixed_coordinate_partial_bound n i j χ houter M hM0 hM k x)))
    (Eventually.of_forall fun x => by
      have hc := (sobolevFisher_cutoff_pointwise n i χ hχ0 M hM x).1
      have hd := (sobolevFisher_cutoff_pointwise n i χ hχ0 M hM x).2
      simpa only [weakRelativeScore_coordinateCutoff_partial, mul_one, mul_zero, add_zero] using
        (tendsto_const_nhds.mul hc).add (tendsto_const_nhds.mul hd))
  simpa only [integral_const, probReal_univ, one_smul] using h

end AffineFKProof
