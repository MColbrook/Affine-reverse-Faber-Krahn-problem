module

public import AffineFK.OUEntropyDissipationCompact
public import AffineFK.OUEntropyDissipationInformation
public import AffineFK.GaussianEntropyCalculusReferenceIntegral
public import AffineFK.GaussianEntropyCalculusLimitPassage

/-!
# Removing the spatial cutoff from actual truncated OU dissipation

The source input is an actual L2 weak relative score and L2 coordinates.
The proved first-order contraction supplies the uniform positive-time
energy bound. Time measurability of each compact dissipation follows from
its proved interval integrability. Spatial convergence and the uniform
energy bound then justify the time dominated-convergence passage.
Only the scalar entropy truncation remains in the final identity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter Set
open scoped Distributions RealInnerProductSpace Topology Interval

theorem ou_truncated_entropy_dissipation (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (ε L : ℝ) (hε : 0 < ε) (hεL : ε ≤ L)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let D := fun r : ℝ =>
      let a := Real.exp (-r)
      let b := Real.sqrt (1 - Real.exp (-2 * r))
      let q := gaussianSmoothingRelativeDensity n ν a b
      let score := gaussianSmoothingScore n ν a b
      ∫ x, ((q x + ε)⁻¹ - (q x + L)⁻¹) * q x * ‖score x‖ ^ 2
        ∂densityMeasure n (gaussianSmoothingDensity n ν a b)
    let F := fun r : ℝ => ∫ x, entropyTruncation ε L
      (gaussianSmoothingRelativeDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r))) x)
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))
    IntervalIntegrable D volume s t ∧ F s - F t = ∫ r in s..t, D r := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  let q : ℝ → E → ℝ := fun r => gaussianSmoothingRelativeDensity n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r)))
  let score : ℝ → E → E := fun r => gaussianSmoothingScore n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r)))
  let μ : ℝ → Measure E := fun r => densityMeasure n (gaussianSmoothingDensity n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r))))
  let g : ℝ → ℝ := entropyTruncationDeriv ε L
  let w : ℝ → E → ℝ := fun r x => ((q r x + ε)⁻¹ - (q r x + L)⁻¹) * q r x
  let d : ℝ → ℝ := fun r => ∫ x, w r x * ‖score r x‖ ^ 2 ∂μ r
  let F : ℝ → ℝ := fun r => ∫ x, entropyTruncation ε L (q r x) ∂γ
  let I : ℝ := ∫ x, ‖v x‖ ^ 2 ∂ν
  have hI : 0 ≤ I := integral_nonneg (fun x => sq_nonneg ‖v x‖)
  have hL : 0 < L := hε.trans_le hεL
  have hU := ou_entropy_initial_first_moment n ν hxi
  have hinfo (r : ℝ) (hr : 0 < r) : IsProbabilityMeasure (μ r) ∧
      MemLp (score r) 2 (μ r) ∧ (∫ x, ‖score r x‖ ^ 2 ∂μ r) ≤ I :=
    ou_entropy_actual_score_uniform_bound n ν hxi v hv hweak r hr
  have hq (r : ℝ) (hr : 0 < r) := gaussianSmoothingRelativeDensity_properties n ν
    (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r))) (ou_smoothing_scale_domain r hr).2.1
  obtain ⟨B, hB, hBb⟩ := entropyTruncationDeriv_uniform_bound ε L hε hεL
  have hgm : Measurable g := by
    change Measurable (entropyTruncationDeriv ε L)
    unfold entropyTruncationDeriv
    fun_prop
  have hgmq (r : ℝ) (hr : 0 < r) : Measurable (fun x => g (q r x)) :=
    hgm.comp (hq r hr).1.continuous.measurable
  have hgb (r : ℝ) (hr : 0 < r) (x : E) : ‖g (q r x)‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using hBb (q r x) ((hq r hr).2.1 x).le
  have hwm (r : ℝ) (hr : 0 < r) : Measurable (w r) := by
    have hm : Measurable (q r) := (hq r hr).1.continuous.measurable
    dsimp [w]
    fun_prop
  have hw (r : ℝ) (hr : 0 < r) (x : E) : 0 ≤ w r x ∧ w r x ≤ 1 := by
    have hpos : 0 < q r x := (hq r hr).2.1 x
    have hc := entropyTruncation_fisher_coefficient ε L (q r x) hε hεL hpos.le
    have heq : w r x = ((q r x) ^ 2 * ((q r x + ε)⁻¹ - (q r x + L)⁻¹)) / q r x := by
      dsimp [w]
      field_simp [hpos.ne']
    rw [heq]
    exact ⟨div_nonneg hc.1 hpos.le, (div_le_one hpos).mpr hc.2⟩
  obtain ⟨χ, hχ, hχinner, _, M, hM, hgrad⟩ := exists_smooth_unit_cutoff n
  have hχ0 : χ 0 = 1 := hχinner 0 (by simp)
  let Fc : ℕ → ℝ → ℝ := fun k r => ∫ x : E, cutoffSequence χ k x *
    (standardGaussianDensity n x * entropyTruncation ε L (q r x))
  let Dc : ℕ → ℝ → ℝ := fun k r => ∫ x, g (q r x) * ⟪score r x, gradient (cutoffSequence χ k) x⟫ +
    cutoffSequence χ k x * w r x * ‖score r x‖ ^ 2 ∂μ r
  have hCompact (k : ℕ) : IntervalIntegrable (Dc k) volume s t ∧
      Fc k s - Fc k t = ∫ r in s..t, Dc k r := by
    simpa only [Fc, Dc, g, q, w, score, μ, gaussianSmoothingRelativeDensity, ← mul_assoc] using
      ou_truncated_compact_entropy_dissipation n ν hU ε L hε hεL (cutoffSequence χ k) s t hs hst
  have hFs : Tendsto (fun k => Fc k s) atTop (𝓝 (F s)) :=
    gaussian_relative_entropy_spatial_cutoff_tendsto n ν (Real.exp (-s))
      (Real.sqrt (1 - Real.exp (-2 * s))) (ou_smoothing_scale_domain s hs).2.1
      (entropyTruncation ε L) g (fun r hr => entropyTruncation_hasDerivAt ε L r hε hL hr.le)
      (entropyTruncation_at_one ε L hε hL).1 B hB
      (fun r hr => by simpa only [Real.norm_eq_abs] using hBb r hr.le) χ hχ0 hχ
  have hFt : Tendsto (fun k => Fc k t) atTop (𝓝 (F t)) :=
    gaussian_relative_entropy_spatial_cutoff_tendsto n ν (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t))) (ou_smoothing_scale_domain t (hs.trans_le hst)).2.1
      (entropyTruncation ε L) g (fun r hr => entropyTruncation_hasDerivAt ε L r hε hL hr.le)
      (entropyTruncation_at_one ε L hε hL).1 B hB
      (fun r hr => by simpa only [Real.norm_eq_abs] using hBb r hr.le) χ hχ0 hχ
  have hDm (k : ℕ) : AEStronglyMeasurable (Dc k) (volume.restrict (Ioc s t)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mp (hCompact k).1).1
  let C := B * M * (1 + I) + I
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (k : ℕ) : ∀ᵐ r ∂volume.restrict (Ioc s t), ‖Dc k r‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := hs.trans hr.1
    letI : IsProbabilityMeasure (μ r) := (hinfo r hr0).1
    exact entropy_dissipation_cutoff_uniform_bound n (μ r) (score r) (hinfo r hr0).2.1
      (fun x => g (q r x)) (w r) (hgmq r hr0) (hwm r hr0) B hB (hgb r hr0) (hw r hr0)
      χ hχ M hM hgrad I (hinfo r hr0).2.2 k
  have hpoint : ∀ᵐ r ∂volume.restrict (Ioc s t), Tendsto (fun k => Dc k r) atTop (𝓝 (d r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := hs.trans hr.1
    letI : IsProbabilityMeasure (μ r) := (hinfo r hr0).1
    exact entropy_dissipation_cutoff_tendsto n (μ r) (score r) (hinfo r hr0).2.1
      (fun x => g (q r x)) (w r) (hgmq r hr0) (hwm r hr0) B hB (hgb r hr0) (hw r hr0)
      χ hχ0 hχ M hM hgrad
  exact entropy_integrated_cutoff_limit Fc Dc F d s t hst (fun k => (hCompact k).2) hFs hFt hDm
    (fun _ => C) (integrable_const C) hbound hpoint

end AffineFKProof
