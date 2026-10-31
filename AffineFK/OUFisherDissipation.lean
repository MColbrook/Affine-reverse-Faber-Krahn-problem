module

public import AffineFK.OUFisherBochnerTime
public import AffineFK.OUFisherCutoff
public import AffineFK.SobolevFisherIntegration

/-!
# Global integrated ordinary Fisher dissipation along the actual OU law

The time identity is first proved with actual compact tests. Genuine
space/time L1 bounds then justify removal of the spatial cutoff by
dominated convergence and Fubini. The generator boundary uses the proved
support estimate, requiring no additional coordinate moment. No Fisher
derivative or global dissipation identity is an assumption.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set
open scoped Topology Distributions Interval

theorem cutoff_weighted_integral_tendsto_any_map
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (W : Ω → EuclideanSpace ℝ (Fin n)) (hW : Measurable W)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    Tendsto (fun k => ∫ ω, cutoffSequence χ k (W ω) * f ω ∂μ)
      atTop (𝓝 (∫ ω, f ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖f ω‖)
  · intro k
    exact ((cutoffSequence χ k).continuous.stronglyMeasurable.comp_measurable hW).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact hf.norm
  · intro k
    exact Filter.Eventually.of_forall fun ω => by
      have hc : ‖cutoffSequence χ k (W ω)‖ ≤ 1 := by
        rw [cutoffSequence_apply, Real.norm_eq_abs, abs_of_nonneg (hχ _).1]
        exact (hχ _).2
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
  · exact Filter.Eventually.of_forall fun ω => by
      have hx : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • W ω) atTop (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
        simpa only [zero_smul] using tendsto_inverse_succ.smul_const (W ω)
      have hc : Tendsto (fun k => cutoffSequence χ k (W ω)) atTop (𝓝 (1 : ℝ)) := by
        simpa only [Function.comp_def, cutoffSequence_apply, hχ0] using (χ.continuous.tendsto 0).comp hx
      simpa only [one_mul] using hc.mul_const (f ω)

theorem ou_ordinary_fisher_dissipation_integrated (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
      gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
    let J : ℝ → ℝ := fun r => ∫ x, ‖gradient (fun y => Real.log (ρ r y)) x‖ ^ 2 * ρ r x
    let K : ℝ → ℝ := fun r => ∫ x, ρ r x * matrixHilbertSchmidtSq (densityLogHessian n (ρ r) x)
    IntervalIntegrable J volume s t ∧ IntervalIntegrable K volume s t ∧
      J t - J s = ∫ r in s..t, 2 * J r - 2 * K r := by
  let E := EuclideanSpace ℝ (Fin n)
  let ρ : ℝ → E → ℝ := fun r => gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
  let f : ℝ → E → ℝ := fun r x => ‖gradient (fun y => Real.log (ρ r y)) x‖ ^ 2 * ρ r x
  let g : ℝ → E → ℝ := fun r x => ρ r x * matrixHilbertSchmidtSq (densityLogHessian n (ρ r) x)
  let J : ℝ → ℝ := fun r => ∫ x, f r x
  let K : ℝ → ℝ := fun r => ∫ x, g r x
  let μT := volume.restrict (Ioc s t)
  let μ := μT.prod (volume : Measure E)
  have hFi : Integrable (fun p : ℝ × E => f p.1 p.2) μ := ou_ordinary_fisher_density_integrable_prod n ν s t hs
  have hGi : Integrable (fun p : ℝ × E => g p.1 p.2) μ := ou_logHessian_energy_density_integrable_prod n ν s t hs
  have hJi : Integrable J μT := hFi.integral_prod_left
  have hKi : Integrable K μT := hGi.integral_prod_left
  have hJI : IntervalIntegrable J volume s t := (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr hJi
  have hKI : IntervalIntegrable K volume s t := (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr hKi
  obtain ⟨χ, hχ, hχinner, houter, M, hM, hgrad⟩ := exists_smooth_unit_cutoff n
  have hχ0 : χ 0 = 1 := hχinner 0 (by simp)
  obtain ⟨C, hC, hCb⟩ := ouTestGenerator_cutoffSequence_uniform_bound n χ houter M hM hgrad
  let B : ℕ → ℝ × E → ℝ := fun k p => ouTestGenerator n (cutoffSequence χ k) p.2 * f p.1 p.2
  let Cf : ℕ → ℝ × E → ℝ := fun k p => cutoffSequence χ k p.2 * f p.1 p.2
  let Cg : ℕ → ℝ × E → ℝ := fun k p => cutoffSequence χ k p.2 * g p.1 p.2
  let D : ℕ → ℝ → ℝ := fun k r => (∫ x, B k (r, x)) +
    2 * (∫ x, Cf k (r, x)) - 2 * (∫ x, Cg k (r, x))
  let Fc : ℕ → ℝ → ℝ := fun k r => ∫ x, cutoffSequence χ k x * f r x
  have hc (k : ℕ) (x : E) : ‖cutoffSequence χ k x‖ ≤ 1 := by
    rw [cutoffSequence_apply, Real.norm_eq_abs, abs_of_nonneg (hχ _).1]
    exact (hχ _).2
  have hBi (k : ℕ) : Integrable (B k) μ := by
    exact (hFi.mul_bdd ((ouTestGenerator n (cutoffSequence χ k)).continuous.comp continuous_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hCb k p.2)).congr (Filter.Eventually.of_forall fun p => mul_comm _ _)
  have hCfi (k : ℕ) : Integrable (Cf k) μ := by
    exact (hFi.mul_bdd ((cutoffSequence χ k).continuous.comp continuous_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hc k p.2)).congr (Filter.Eventually.of_forall fun p => mul_comm _ _)
  have hCgi (k : ℕ) : Integrable (Cg k) μ := by
    exact (hGi.mul_bdd ((cutoffSequence χ k).continuous.comp continuous_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hc k p.2)).congr (Filter.Eventually.of_forall fun p => mul_comm _ _)
  have hFTC (k : ℕ) : (∫ r in s..t, D k r) = Fc k t - Fc k s :=
    (ou_ordinary_fisher_compact_bochner_integral n ν hU (cutoffSequence χ k) s t hs hst).2
  have hEq (k : ℕ) : (∫ r in s..t, D k r) =
      (∫ p, B k p ∂μ) + 2 * (∫ p, Cf k p ∂μ) - 2 * (∫ p, Cg k p ∂μ) := by
    rw [intervalIntegral.integral_of_le hst]
    change (∫ r, (∫ x, B k (r, x)) + 2 * (∫ x, Cf k (r, x)) - 2 * (∫ x, Cg k (r, x)) ∂μT) = _
    rw [integral_sub (f := fun r => (∫ x, B k (r, x)) + 2 * (∫ x, Cf k (r, x)))
      (g := fun r => 2 * (∫ x, Cg k (r, x)))
        ((hBi k).integral_prod_left.add ((hCfi k).integral_prod_left.const_mul 2))
        ((hCgi k).integral_prod_left.const_mul 2),
      integral_add (f := fun r => ∫ x, B k (r, x))
        (g := fun r => 2 * (∫ x, Cf k (r, x)))
          (hBi k).integral_prod_left ((hCfi k).integral_prod_left.const_mul 2),
      integral_const_mul, integral_const_mul,
      ← integral_prod (B k) (hBi k), ← integral_prod (Cf k) (hCfi k), ← integral_prod (Cg k) (hCgi k)]
  have hBlim : Tendsto (fun k => ∫ p, B k p ∂μ) atTop (𝓝 0) := by
    simpa only [B, mul_comm] using ouTestGenerator_cutoff_weighted_integral_tendsto_zero
      μ n Prod.snd measurable_snd (fun p => f p.1 p.2) hFi χ hχ0 houter M hM hgrad
  have hFlim := cutoff_weighted_integral_tendsto_any_map μ n Prod.snd measurable_snd
    (fun p => f p.1 p.2) hFi χ hχ0 hχ
  have hGlim := cutoff_weighted_integral_tendsto_any_map μ n Prod.snd measurable_snd
    (fun p => g p.1 p.2) hGi χ hχ0 hχ
  have hDlim : Tendsto (fun k => ∫ r in s..t, D k r) atTop
      (𝓝 (2 * (∫ p, f p.1 p.2 ∂μ) - 2 * (∫ p, g p.1 p.2 ∂μ))) := by
    simpa only [hEq, zero_add, Cf, Cg] using (hBlim.add (hFlim.const_mul 2)).sub (hGlim.const_mul 2)
  have hFpoint (r : ℝ) (hr : 0 < r) : Tendsto (fun k => Fc k r) atTop (𝓝 (J r)) := by
    have hi := (gaussianSmoothing_fisher_energy_densities_integrable n ν (Real.exp (-r))
      (Real.sqrt (1 - Real.exp (-2 * r))) (ou_smoothing_scale_domain r hr).2.1).1
    simpa only [Fc, J, mul_comm] using sobolevFisher_cutoff_integral_tendsto n volume (f r) hi χ hχ0 hχ
  have hEnd : Tendsto (fun k => ∫ r in s..t, D k r) atTop (𝓝 (J t - J s)) := by
    simpa only [hFTC] using (hFpoint t (hs.trans_le hst)).sub (hFpoint s hs)
  have hValue := tendsto_nhds_unique hEnd hDlim
  refine ⟨hJI, hKI, hValue.trans ?_⟩
  rw [intervalIntegral.integral_of_le hst]
  change _ = ∫ r, 2 * J r - 2 * K r ∂μT
  rw [integral_sub (f := fun r => 2 * J r) (g := fun r => 2 * K r)
    (hJi.const_mul 2) (hKi.const_mul 2), integral_const_mul, integral_const_mul,
    ← integral_prod (fun p : ℝ × E => f p.1 p.2) hFi,
    ← integral_prod (fun p : ℝ × E => g p.1 p.2) hGi]

end AffineFKProof
