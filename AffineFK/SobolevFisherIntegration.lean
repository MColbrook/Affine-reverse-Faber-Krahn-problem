module

public import AffineFK.SobolevFisherIntegrationCutoff

/-!
# Global coordinate integration for a genuine weak density derivative

Compact coordinate cutoffs extend the distributional integration identity
to a coordinate. The boundary term is dominated by a constant times the
integrable density; no first moment is required for this step.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

theorem sobolevFisher_cutoff_integral_tendsto (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : Integrable h μ)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    Tendsto (fun k => ∫ x, h x * cutoffSequence χ k x ∂μ) atTop (𝓝 (∫ x, h x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖h x‖)
  · intro k
    exact hh.aestronglyMeasurable.mul (cutoffSequence χ k).continuous.aestronglyMeasurable
  · exact hh.norm
  · intro k
    exact Eventually.of_forall fun x => by
      have hc : ‖cutoffSequence χ k x‖ ≤ 1 := by
        rw [cutoffSequence_apply, Real.norm_eq_abs, abs_of_nonneg (hχ _).1]
        exact (hχ _).2
      rw [norm_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (norm_nonneg (h x))
  · exact Eventually.of_forall fun x => by
      have hx : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) atTop
          (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
        simpa only [zero_smul] using tendsto_inverse_succ.smul_const x
      have hc : Tendsto (fun k => cutoffSequence χ k x) atTop (𝓝 (1 : ℝ)) := by
        simpa only [Function.comp_def, cutoffSequence_apply, hχ0] using (χ.continuous.tendsto 0).comp hx
      simpa only [mul_one] using tendsto_const_nhds.mul hc

theorem sobolevFisher_boundary_integral_tendsto (n : ℕ) (i : Fin n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : Integrable ρ μ)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (houter : ∀ x, 2 ≤ ‖x‖ → χ x = 0)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M) :
    Tendsto (fun k => ∫ x, ρ x * (x i * partialTest n i (cutoffSequence χ k) x) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have h := tendsto_integral_of_dominated_convergence
    (F := fun k x => ρ x * (x i * partialTest n i (cutoffSequence χ k) x))
    (f := fun _ => (0 : ℝ)) (fun x => ‖ρ x‖ * (2 * M))
    (fun k => hρ.aestronglyMeasurable.mul
      (show Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
        x i * partialTest n i (cutoffSequence χ k) x) from by fun_prop).aestronglyMeasurable)
    (hρ.norm.mul_const (2 * M))
    (fun k => Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (sobolevFisher_coordinate_partial_bound n i χ houter M hM0 hM k x) (norm_nonneg (ρ x)))
    (Eventually.of_forall fun x => by
      simpa only [mul_zero] using tendsto_const_nhds.mul
        (tendsto_const_nhds.mul (sobolevFisher_cutoff_pointwise n i χ hχ0 M hM x).2))
  simpa only [integral_zero] using h

theorem sobolevFisher_coordinate_integral (n : ℕ) (i : Fin n)
    (ρ g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (_hg : Integrable g (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hxg : Integrable (fun x => x i * g x) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hweak : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, ρ x * partialTest n i φ x) = -(∫ x, g x * φ x)) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i * g x) = -(∫ x, ρ x) := by
  obtain ⟨χ, hχ, hinner, houter, M, hM0, hM⟩ := exists_smooth_unit_cutoff n
  have hχ0 : χ 0 = 1 := hinner 0 (by simp)
  have hc (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ‖cutoffSequence χ k x‖ ≤ 1 := by
    rw [cutoffSequence_apply, Real.norm_eq_abs, abs_of_nonneg (hχ _).1]
    exact (hχ _).2
  have hA (k : ℕ) : Integrable (fun x => ρ x * cutoffSequence χ k x) :=
    hρ.mul_bdd (cutoffSequence χ k).continuous.aestronglyMeasurable (Eventually.of_forall fun x => hc k x)
  have hB (k : ℕ) : Integrable (fun x => ρ x * (x i * partialTest n i (cutoffSequence χ k) x)) :=
    hρ.mul_bdd (show Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      x i * partialTest n i (cutoffSequence χ k) x) from by fun_prop).aestronglyMeasurable
      (Eventually.of_forall fun x => sobolevFisher_coordinate_partial_bound n i χ houter M hM0 hM k x)
  have heq (k : ℕ) : (∫ x, ρ x * cutoffSequence χ k x) +
      (∫ x, ρ x * (x i * partialTest n i (cutoffSequence χ k) x)) =
        -(∫ x, (x i * g x) * cutoffSequence χ k x) := by
    calc
      _ = ∫ x, ρ x * cutoffSequence χ k x +
          ρ x * (x i * partialTest n i (cutoffSequence χ k) x) := (integral_add (hA k) (hB k)).symm
      _ = ∫ x, ρ x * partialTest n i (coordinateCutoff n i χ k) x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change ρ x * cutoffSequence χ k x + ρ x * (x i * partialTest n i (cutoffSequence χ k) x) =
            ρ x * partialTest n i (coordinateCutoff n i χ k) x
          rw [sobolevFisher_coordinateCutoff_partial]
          ring
      _ = -(∫ x, g x * coordinateCutoff n i χ k x) := hweak _
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change g x * coordinateCutoff n i χ k x = (x i * g x) * cutoffSequence χ k x
          rw [coordinateCutoff_apply]
          ring
  have hleft := (sobolevFisher_cutoff_integral_tendsto n volume ρ hρ χ hχ0 hχ).add
    (sobolevFisher_boundary_integral_tendsto n i volume ρ hρ χ hχ0 houter M hM0 hM)
  have hleft' : Tendsto (fun k => -(∫ x, (x i * g x) * cutoffSequence χ k x)) atTop
      (𝓝 (∫ x, ρ x)) := by
    simpa only [heq, add_zero] using hleft
  have hright := (sobolevFisher_cutoff_integral_tendsto n volume (fun x => x i * g x) hxg χ hχ0 hχ).neg
  have hl := tendsto_nhds_unique hleft' hright
  linarith

theorem sobolevFisher_density_mass (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hρ0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)] : (∫ x, ρ x) = 1 := by
  have heq := integral_withDensity_eq_integral_toReal_smul₀
    hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top (r := ρ x))
    (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
  have hmass : (∫ x, (1 : ℝ) ∂densityMeasure n ρ) = ∫ x, ρ x := by
    refine heq.trans (integral_congr_ae ?_)
    filter_upwards [hρ0] with x hx
    rw [ENNReal.toReal_ofReal hx]
    simp only [smul_eq_mul, mul_one]
  simpa only [integral_const, probReal_univ, one_smul] using hmass.symm

theorem sobolevFisher_coordinate_integral_probability_density (n : ℕ) (i : Fin n)
    (ρ g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hρ0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hg : Integrable g (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hxg : Integrable (fun x => x i * g x) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hweak : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, ρ x * partialTest n i φ x) = -(∫ x, g x * φ x)) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i * g x) = -1 := by
  rw [sobolevFisher_coordinate_integral n i ρ g hρ hg hxg hweak, sobolevFisher_density_mass n ρ hρ hρ0]

end AffineFKProof
