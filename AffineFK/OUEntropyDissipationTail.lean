module

public import AffineFK.OUEntropyDissipation
public import AffineFK.OUEntropyEndpoints
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Actual integrable OU score energy and the infinite-time entropy tail

The positive-time Fisher bound is the proved first-order contraction.
Local integrability follows from the genuine de Bruijn theorem, and the
exponential bound gives integrability on the whole positive half-line.
The infinite-time KL endpoint is used only at zero, where toReal is
continuous. No finite initial KL assumption enters this development.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter Set
open scoped Distributions RealInnerProductSpace Topology Interval ENNReal

/-- The real squared norm of the actual logarithmic relative score under
the actual OU law. Its positive-time and half-line integrability are proved. -/
def ouScoreEnergy (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) : ℝ :=
  ∫ x, ‖gaussianSmoothingScore n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) x‖ ^ 2
    ∂ouInitialLaw n ν t

theorem ouScoreEnergy_nonneg (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    0 ≤ ouScoreEnergy n ν t := integral_nonneg (fun x => sq_nonneg _)

theorem ouScoreEnergy_integrable_Ioi (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) :
    IntegrableOn (ouScoreEnergy n ν) (Ioi 0) volume := by
  let I := ouScoreEnergy n ν
  let S : ℝ := ∫ x, ‖v x‖ ^ 2 ∂ν
  have hS : 0 ≤ S := integral_nonneg (fun x => sq_nonneg _)
  have hlocal : LocallyIntegrableOn I (Ioi 0) volume := by
    intro r hr
    change 0 < r at hr
    have h := (ou_entropy_dissipation n ν hxi v hv hweak (r / 2) (r + 1)
      (by linarith) (by linarith)).2.2.1
    refine ⟨Ioc (r / 2) (r + 1), mem_nhdsWithin_of_mem_nhds (Ioc_mem_nhds (by linarith) (by linarith)), ?_⟩
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp h
  have hJ : IntegrableOn (fun r : ℝ => S * Real.exp (-2 * r)) (Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 0).const_mul S
  apply hJ.mono' hlocal.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (ouScoreEnergy_nonneg n ν r)]
  have h := (OU_firstOrder_relative_score_information_bound n ν hxi v hv hweak r hr).2
  simpa only [ouScoreEnergy, ouInitialLaw, mul_comm] using h

theorem ouScoreEnergy_integral_le (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (s : ℝ) (hs : 0 ≤ s) :
    (∫ r in Ioi s, ouScoreEnergy n ν r) ≤
      (Real.exp (-2 * s) / 2) * (∫ x, ‖v x‖ ^ 2 ∂ν) := by
  let S : ℝ := ∫ x, ‖v x‖ ^ 2 ∂ν
  have hI : IntegrableOn (ouScoreEnergy n ν) (Ioi s) volume :=
    (ouScoreEnergy_integrable_Ioi n ν hxi v hv hweak).mono_set (fun r hr => lt_of_le_of_lt hs hr)
  have hJ : IntegrableOn (fun r : ℝ => S * Real.exp (-2 * r)) (Ioi s) volume :=
    (integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) s).const_mul S
  have h := integral_mono_ae hI hJ (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have h := (OU_firstOrder_relative_score_information_bound n ν hxi v hv hweak r (hs.trans_lt hr)).2
    simpa only [ouScoreEnergy, ouInitialLaw, mul_comm] using h)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) s] at h
  convert h using 1 <;> dsimp [S] <;> ring

theorem ou_positive_entropy_eq_score_tail (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (s : ℝ) (hs : 0 < s) :
    (klDiv (ouInitialLaw n ν s) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal =
      ∫ r in Ioi s, ouScoreEnergy n ν r := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let H : ℝ → ℝ := fun r => (klDiv (ouInitialLaw n ν r) γ).toReal
  have hU : MemLp (fun u : EuclideanSpace ℝ (Fin n) => u) 2 ν := memLp_piLp_iff.mpr hxi
  have hsecond := (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU
  have hH : Tendsto H atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
      (ou_gaussian_entropy_tendsto_zero n ν hsecond)
    simpa only [H, γ, ouInitialLaw, ENNReal.toReal_zero, Function.comp_def] using! h
  have hI : IntegrableOn (ouScoreEnergy n ν) (Ioi s) volume :=
    (ouScoreEnergy_integrable_Ioi n ν hxi v hv hweak).mono_set (fun r hr => hs.trans hr)
  have hlim := intervalIntegral_tendsto_integral_Ioi s hI tendsto_id
  have hEq : (fun t : ℝ => H s - H t) =ᶠ[atTop]
      (fun t => ∫ r in s..t, ouScoreEnergy n ν r) := by
    filter_upwards [eventually_ge_atTop s] with t ht
    exact (ou_entropy_dissipation n ν hxi v hv hweak s t hs ht).2.2.2
  have hlimH : Tendsto (fun t : ℝ => H s - H t) atTop (𝓝 (H s)) := by
    simpa only [sub_zero] using hH.const_sub (H s)
  exact tendsto_nhds_unique hlimH (hlim.congr' hEq.symm)

end AffineFKProof
