module

public import AffineFK.OUEntropyDissipationSpatial
public import AffineFK.GaussianEntropyCalculusKLFormula
public import AffineFK.EntropyTruncationLimits

/-!
# Scalar truncation limit in the actual positive-time OU entropy identity

Only elementary convergence premises on the two scalar truncation sequences
are supplied here. The probability laws, score fields, KL integrability,
time domination and entropy identity are all proved. A final concrete
sequence specialization must discharge the scalar convergence premises.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter Set
open scoped Distributions RealInnerProductSpace Topology Interval ENNReal

theorem ou_entropy_dissipation_of_scalar_limits (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (ε L : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hεL : ∀ k, ε k ≤ L k)
    (hψlim : ∀ r : ℝ, 0 < r → Tendsto (fun k => entropyTruncation (ε k) (L k) r) atTop (𝓝 (klFun r)))
    (hwlim : ∀ r : ℝ, 0 < r → Tendsto (fun k => ((r + ε k)⁻¹ - (r + L k)⁻¹) * r) atTop (𝓝 1))
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let μ := fun r : ℝ => (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => Real.exp (-r) • p.1 + Real.sqrt (1 - Real.exp (-2 * r)) • p.2)
    let I := fun r : ℝ => ∫ x, ‖gaussianSmoothingScore n ν (Real.exp (-r))
      (Real.sqrt (1 - Real.exp (-2 * r))) x‖ ^ 2 ∂μ r
    klDiv (μ s) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    klDiv (μ t) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    IntervalIntegrable I volume s t ∧
    (klDiv (μ s) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal -
      (klDiv (μ t) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal = ∫ r in s..t, I r := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  let q : ℝ → E → ℝ := fun r => gaussianSmoothingRelativeDensity n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r)))
  let score : ℝ → E → E := fun r => gaussianSmoothingScore n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r)))
  let μ : ℝ → Measure E := fun r => densityMeasure n (gaussianSmoothingDensity n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r))))
  let μmap : ℝ → Measure E := fun r => (ν.prod γ).map
    (fun p => Real.exp (-r) • p.1 + Real.sqrt (1 - Real.exp (-2 * r)) • p.2)
  let H : ℝ → ℝ := fun r => (klDiv (μmap r) γ).toReal
  let I : ℝ → ℝ := fun r => ∫ x, ‖score r x‖ ^ 2 ∂μ r
  let I0 : ℝ := ∫ x, ‖v x‖ ^ 2 ∂ν
  have hU2 : MemLp (fun u : E => u) 2 ν := memLp_piLp_iff.mpr hxi
  have hsecond : Integrable (fun u : E => ‖u‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hU2.aestronglyMeasurable).mp hU2
  have hL (k : ℕ) : 0 < L k := (hε k).trans_le (hεL k)
  have hlaw (r : ℝ) (hr : 0 < r) : μmap r = μ r :=
    gaussianSmoothingDensity_law n ν _ _ (ou_smoothing_scale_domain r hr).2.1
  have hKL (r : ℝ) (hr : 0 < r) : klDiv (μmap r) γ ≠ ∞ ∧
      Integrable (fun x => klFun (q r x)) γ ∧ H r = ∫ x, klFun (q r x) ∂γ :=
    gaussian_relative_smoothing_entropy_formula n ν hsecond _ _ (ou_smoothing_scale_domain r hr).2.1
  have hinfo (r : ℝ) (hr : 0 < r) : IsProbabilityMeasure (μ r) ∧
      MemLp (score r) 2 (μ r) ∧ I r ≤ I0 :=
    ou_entropy_actual_score_uniform_bound n ν hxi v hv hweak r hr
  have hq (r : ℝ) (hr : 0 < r) := gaussianSmoothingRelativeDensity_properties n ν
    (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r))) (ou_smoothing_scale_domain r hr).2.1
  let w : ℕ → ℝ → E → ℝ := fun k r x => ((q r x + ε k)⁻¹ - (q r x + L k)⁻¹) * q r x
  have hw (k : ℕ) (r : ℝ) (hr : 0 < r) (x : E) : 0 ≤ w k r x ∧ w k r x ≤ 1 := by
    have hpos := (hq r hr).2.1 x
    have hc := entropyTruncation_fisher_coefficient (ε k) (L k) (q r x) (hε k) (hεL k) hpos.le
    have heq : w k r x = ((q r x) ^ 2 * ((q r x + ε k)⁻¹ - (q r x + L k)⁻¹)) / q r x := by
      dsimp [w]
      field_simp [hpos.ne']
    rw [heq]
    exact ⟨div_nonneg hc.1 hpos.le, (div_le_one hpos).mpr hc.2⟩
  let F : ℕ → ℝ → ℝ := fun k r => ∫ x, entropyTruncation (ε k) (L k) (q r x) ∂γ
  let D : ℕ → ℝ → ℝ := fun k r => ∫ x, w k r x * ‖score r x‖ ^ 2 ∂μ r
  have hFTC (k : ℕ) : IntervalIntegrable (D k) volume s t ∧ F k s - F k t = ∫ r in s..t, D k r :=
    ou_truncated_entropy_dissipation n ν hxi v hv hweak (ε k) (L k) (hε k) (hεL k) s t hs hst
  have hFpoint (r : ℝ) (hr : 0 < r) : Tendsto (fun k => F k r) atTop (𝓝 (H r)) := by
    have hm (k : ℕ) : AEStronglyMeasurable (fun x => entropyTruncation (ε k) (L k) (q r x)) γ := by
      have hc : Continuous (fun x => entropyTruncation (ε k) (L k) (q r x)) := by
        apply continuous_iff_continuousAt.mpr
        intro x
        exact (entropyTruncation_contDiffAt (ε k) (L k) (q r x) (hε k) (hL k)
          ((hq r hr).2.1 x).le).continuousAt.comp (hq r hr).1.continuous.continuousAt
      exact hc.aestronglyMeasurable
    have hb (k : ℕ) : ∀ᵐ x ∂γ, ‖entropyTruncation (ε k) (L k) (q r x)‖ ≤ klFun (q r x) := by
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (entropyTruncation_nonneg (ε k) (L k) (q r x)
          (hε k) (hεL k) ((hq r hr).2.1 x).le)]
        exact entropyTruncation_le_klFun (ε k) (L k) (q r x) (hε k) (hεL k) ((hq r hr).2.1 x).le
    have h := tendsto_integral_of_dominated_convergence (fun x => klFun (q r x)) hm (hKL r hr).2.1 hb
      (Filter.Eventually.of_forall fun x => hψlim (q r x) ((hq r hr).2.1 x))
    simpa only [← (hKL r hr).2.2] using h
  have hDm (k : ℕ) : AEStronglyMeasurable (D k) (volume.restrict (Ioc s t)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mp (hFTC k).1).1
  have hpoint : ∀ᵐ r ∂volume.restrict (Ioc s t), Tendsto (fun k => D k r) atTop (𝓝 (I r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := hs.trans hr.1
    letI : IsProbabilityMeasure (μ r) := (hinfo r hr0).1
    have hsq : Integrable (fun x => ‖score r x‖ ^ 2) (μ r) :=
      (memLp_two_iff_integrable_sq_norm (hinfo r hr0).2.1.aestronglyMeasurable).mp (hinfo r hr0).2.1
    apply tendsto_integral_of_dominated_convergence (fun x => ‖score r x‖ ^ 2)
    · intro k
      have hwm : Measurable (w k r) := by
        have hqm : Measurable (q r) := (hq r hr0).1.continuous.measurable
        dsimp [w]
        fun_prop
      exact hwm.aestronglyMeasurable.mul ((hinfo r hr0).2.1.aestronglyMeasurable.norm.pow 2)
    · exact hsq
    · intro k
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw k r hr0 x).1 (sq_nonneg _))]
        exact mul_le_of_le_one_left (sq_nonneg _) (hw k r hr0 x).2
    · exact Filter.Eventually.of_forall fun x => by
        simpa only [one_mul] using (hwlim (q r x) ((hq r hr0).2.1 x)).mul_const (‖score r x‖ ^ 2)
  have hbound (k : ℕ) : ∀ᵐ r ∂volume.restrict (Ioc s t), ‖D k r‖ ≤ I0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := hs.trans hr.1
    have hsq : Integrable (fun x => ‖score r x‖ ^ 2) (μ r) :=
      (memLp_two_iff_integrable_sq_norm (hinfo r hr0).2.1.aestronglyMeasurable).mp (hinfo r hr0).2.1
    refine (norm_integral_le_of_norm_le hsq (Filter.Eventually.of_forall fun x => ?_)).trans
      (hinfo r hr0).2.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw k r hr0 x).1 (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (hw k r hr0 x).2
  have hfinal := entropy_integrated_cutoff_limit F D H I s t hst (fun k => (hFTC k).2)
    (hFpoint s hs) (hFpoint t (hs.trans_le hst)) hDm (fun _ => I0) (integrable_const I0) hbound hpoint
  have hIeq : I =ᵐ[volume.restrict (Ι s t)]
      (fun r => ∫ x, ‖score r x‖ ^ 2 ∂μmap r) := by
    rw [uIoc_of_le hst]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [hlaw r (hs.trans hr.1)]
  exact ⟨(hKL s hs).1, (hKL t (hs.trans_le hst)).1, hfinal.1.congr_ae hIeq,
    hfinal.2.trans (intervalIntegral.integral_congr_ae_restrict hIeq)⟩

end AffineFKProof
