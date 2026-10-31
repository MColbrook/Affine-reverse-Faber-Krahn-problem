module

public import AffineFK.SobolevCoordinates
public import AffineFK.WeightedTestIntegration

/-!
# Coordinate cutoffs for global weak integration by parts

The product of a coordinate and a cutoff partial derivative is uniformly
bounded, without requiring a first moment of the density. Outside the
fixed support ball the genuine derivative is zero; inside it the scaled
coordinate is bounded. The cutoff value and partial derivative have their
actual pointwise limits.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

theorem sobolevFisher_cutoff_gradient_zero (n : ℕ)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (houter : ∀ x, 2 ≤ ‖x‖ → χ x = 0)
    (z : EuclideanSpace ℝ (Fin n)) (hz : 2 < ‖z‖) : gradient χ z = 0 := by
  have hU : {y : EuclideanSpace ℝ (Fin n) | 2 < ‖y‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  have heq : (χ : EuclideanSpace ℝ (Fin n) → ℝ) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [hU] with y hy
    exact houter y hy.le
  have hd : fderiv ℝ χ z = 0 := by simpa using heq.fderiv_eq (𝕜 := ℝ)
  rw [gradient, hd, map_zero]

theorem sobolevFisher_base_coordinate_partial_bound (n : ℕ) (i : Fin n)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (houter : ∀ x, 2 ≤ ‖x‖ → χ x = 0)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M)
    (z : EuclideanSpace ℝ (Fin n)) : ‖z i * partialTest n i χ z‖ ≤ 2 * M := by
  by_cases hz : ‖z‖ ≤ 2
  · have hp : ‖partialTest n i χ z‖ ≤ M := by
      rw [partialTest_apply]
      exact (PiLp.norm_apply_le (gradient χ z) i).trans (hM z)
    rw [norm_mul]
    exact (mul_le_mul (PiLp.norm_apply_le z i) hp (norm_nonneg _) (norm_nonneg z)).trans
      (mul_le_mul_of_nonneg_right hz hM0)
  · rw [partialTest_apply, sobolevFisher_cutoff_gradient_zero n χ houter z (lt_of_not_ge hz)]
    simp only [PiLp.zero_apply, mul_zero, norm_zero]
    positivity

theorem sobolevFisher_scaled_partial (n : ℕ) (i : Fin n)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n i (cutoffSequence χ k) x =
      ((k : ℝ) + 1)⁻¹ * partialTest n i χ (((k : ℝ) + 1)⁻¹ • x) := by
  rw [partialTest_apply]
  change gradient (scaledTestFunction ((k : ℝ) + 1) (by positivity) χ) x i = _
  rw [gradient_scaledTestFunction]
  simp only [PiLp.smul_apply, smul_eq_mul, partialTest_apply]

theorem sobolevFisher_coordinate_partial_bound (n : ℕ) (i : Fin n)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (houter : ∀ x, 2 ≤ ‖x‖ → χ x = 0)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x i * partialTest n i (cutoffSequence χ k) x‖ ≤ 2 * M := by
  have heq : x i * partialTest n i (cutoffSequence χ k) x =
      ((((k : ℝ) + 1)⁻¹ • x) i) * partialTest n i χ (((k : ℝ) + 1)⁻¹ • x) := by
    rw [sobolevFisher_scaled_partial]
    change x i * (_ * _) = (_ * x i) * _
    ring
  rw [heq]
  exact sobolevFisher_base_coordinate_partial_bound n i χ houter M hM0 hM _

theorem sobolevFisher_cutoff_pointwise (n : ℕ) (i : Fin n)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (M : ℝ) (hM : ∀ x, ‖gradient χ x‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => cutoffSequence χ k x) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun k => partialTest n i (cutoffSequence χ k) x) atTop (𝓝 (0 : ℝ)) := by
  have hx : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) atTop
      (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
    simpa only [zero_smul] using tendsto_inverse_succ.smul_const x
  have hc : Tendsto (fun k => cutoffSequence χ k x) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, cutoffSequence_apply, hχ0] using (χ.continuous.tendsto 0).comp hx
  have hg : Tendsto (fun k => gradient (cutoffSequence χ k) x) atTop
      (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
    have hn := squeeze_zero (fun _ => norm_nonneg _)
      (fun k => gradient_scaledTestFunction_bound _ (by positivity) χ M hM x)
      (show Tendsto (fun k : ℕ => M / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) from by
        simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul tendsto_inverse_succ)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hn
  refine ⟨hc, ?_⟩
  have h := ((coordinateFunctional n i).continuous.tendsto 0).comp hg
  simpa only [Function.comp_def, coordinateFunctional_apply, partialTest_apply, map_zero] using h

theorem sobolevFisher_coordinateCutoff_partial (n : ℕ) (i : Fin n)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n i (coordinateCutoff n i χ k) x =
      cutoffSequence χ k x + x i * partialTest n i (cutoffSequence χ k) x := by
  rw [partialTest_apply, coordinateCutoff_gradient]
  simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.basisFun_apply,
    smul_eq_mul, partialTest_apply]

end AffineFKProof
