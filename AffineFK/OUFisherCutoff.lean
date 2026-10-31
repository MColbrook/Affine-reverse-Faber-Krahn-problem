module

public import AffineFK.AffineTestFunctions
public import AffineFK.WeakRelativeScoreMomentsCutoff
public import AffineFK.OUDensityTimeWeakEquation

/-!
# Removing the OU generator cutoff against an integrable density

The coordinate times first-partial cutoff is uniformly bounded by its
actual derivative support. Second partials have the exact inverse-square
scaling. Thus the generator cutoffs are uniformly bounded and converge
pointwise to zero. Their integrals against any actual L1 function tend
to zero, also after a measurable parameter map. No coordinate moment is
required for this boundary limit. Existing coordinate-support estimates
are reused from the attributed weak-score moment cutoff development.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter
open scoped Distributions Topology

theorem second_partialTest_cutoffSequence (n : ℕ) (i j : Fin n)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n i (partialTest n j (cutoffSequence χ k)) x =
      (((k : ℝ) + 1)⁻¹) ^ 2 *
        partialTest n i (partialTest n j χ) (((k : ℝ) + 1)⁻¹ • x) := by
  change partialTest n i (partialTest n j (scaledTestFunction ((k : ℝ) + 1) (by positivity) χ)) x = _
  rw [partialTest_scaled, partialTest_smul, partialTest_scaled, smul_smul]
  change (((k : ℝ) + 1)⁻¹ * ((k : ℝ) + 1)⁻¹) *
    scaledTestFunction ((k : ℝ) + 1) (by positivity) (partialTest n i (partialTest n j χ)) x = _
  rw [scaledTestFunction_apply, pow_two]

theorem ouTestGenerator_cutoffSequence_uniform_bound (n : ℕ)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (houter : ∀ x, 2 ≤ ‖x‖ → χ x = 0)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
      ‖ouTestGenerator n (cutoffSequence χ k) x‖ ≤ C := by
  let B (i : Fin n) : ℝ := ‖TestFunction.toBoundedContinuousFunctionCLM ℝ (partialTest n i (partialTest n i χ))‖
  let C : ℝ := ∑ i : Fin n, (B i + 2 * M)
  have hB0 (i : Fin n) : 0 ≤ B i := norm_nonneg _
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => add_nonneg (hB0 i) (mul_nonneg (by norm_num) hM0)
  refine ⟨C, hC, ?_⟩
  intro k x
  have hsecond (i : Fin n) : ‖partialTest n i (partialTest n i (cutoffSequence χ k)) x‖ ≤ B i := by
    have hr : 0 < (k : ℝ) + 1 := by positivity
    have hR : 1 ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hinv : ((k : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr hR
    have hscale : (((k : ℝ) + 1)⁻¹) ^ 2 ≤ 1 := by
      have hi : 0 ≤ ((k : ℝ) + 1)⁻¹ := inv_nonneg.mpr hr.le
      nlinarith
    have hb := (TestFunction.toBoundedContinuousFunctionCLM ℝ (partialTest n i (partialTest n i χ))).norm_coe_le_norm
      (((k : ℝ) + 1)⁻¹ • x)
    rw [second_partialTest_cutoffSequence, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (((k : ℝ) + 1)⁻¹) ^ 2 * B i := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ ≤ B i := by nlinarith [hB0 i]
  rw [ouTestGenerator_apply]
  calc
    _ ≤ ∑ i : Fin n, ‖partialTest n i (partialTest n i (cutoffSequence χ k)) x -
        x i * partialTest n i (cutoffSequence χ k) x‖ := norm_sum_le _ _
    _ ≤ C := Finset.sum_le_sum fun i _ => (norm_sub_le _ _).trans
      (add_le_add (hsecond i) (weakRelativeScore_mixed_coordinate_partial_bound n i i χ houter M hM0 hM k x))

theorem ouTestGenerator_cutoffSequence_tendsto_zero (n : ℕ)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (M : ℝ) (hM : ∀ x, ‖gradient χ x‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k : ℕ => ouTestGenerator n (cutoffSequence χ k) x) atTop (𝓝 0) := by
  have harg : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) atTop (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
    simpa only [zero_smul] using tendsto_inverse_succ.smul_const x
  have hsecond (i : Fin n) : Tendsto (fun k : ℕ =>
      partialTest n i (partialTest n i (cutoffSequence χ k)) x) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_inverse_succ.pow 2).mul
      (((partialTest n i (partialTest n i χ)).continuous.tendsto 0).comp harg)
    simpa only [second_partialTest_cutoffSequence, Function.comp_def, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using h
  have hrow (i : Fin n) : Tendsto (fun k : ℕ =>
      partialTest n i (partialTest n i (cutoffSequence χ k)) x -
        x i * partialTest n i (cutoffSequence χ k) x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using (hsecond i).sub
      ((sobolevFisher_cutoff_pointwise n i χ hχ0 M hM x).2.const_mul (x i))
  simpa only [ouTestGenerator_apply, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ => hrow i)

theorem ouTestGenerator_cutoff_weighted_integral_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (W : Ω → EuclideanSpace ℝ (Fin n)) (hW : Measurable W)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (houter : ∀ x, 2 ≤ ‖x‖ → χ x = 0)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M) :
    Tendsto (fun k : ℕ => ∫ ω, f ω * ouTestGenerator n (cutoffSequence χ k) (W ω) ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := ouTestGenerator_cutoffSequence_uniform_bound n χ houter M hM0 hM
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun k ω => f ω * ouTestGenerator n (cutoffSequence χ k) (W ω))
    (f := fun _ => (0 : ℝ)) (fun ω => C * ‖f ω‖)
    (fun k => hf.aestronglyMeasurable.mul
      ((ouTestGenerator n (cutoffSequence χ k)).continuous.stronglyMeasurable.comp_measurable hW).aestronglyMeasurable)
    (hf.norm.const_mul C)
    (fun k => Filter.Eventually.of_forall fun ω => by
      change ‖f ω * ouTestGenerator n (cutoffSequence χ k) (W ω)‖ ≤ C * ‖f ω‖
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hbound k (W ω)) (norm_nonneg _)).trans_eq (mul_comm _ _))
    (Filter.Eventually.of_forall fun ω => by
      simpa only [mul_zero] using
        (ouTestGenerator_cutoffSequence_tendsto_zero n χ hχ0 M hM (W ω)).const_mul (f ω))
  simpa only [integral_zero] using h

end AffineFKProof
