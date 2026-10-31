module

public import AffineFK.OUEntropyDissipationInitial

/-!
# The actual full OU entropy-dissipation integral

The initial KL bound and finiteness are proved before applying continuity
of toReal at the initial endpoint. The infinite-time endpoint has already
identified every positive-time entropy with its actual score-energy tail.
Dominated convergence of these tails then supplies the full half-line
integral. No finite initial entropy, Gaussian LSI or entropy identity is
an assumption.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter Set
open scoped Distributions RealInnerProductSpace Topology ENNReal

theorem ou_score_tail_tendsto_zero_sequence (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) :
    Tendsto (fun k : ℕ => ∫ r in Ioi (((k : ℝ) + 1)⁻¹), ouScoreEnergy n ν r) atTop
      (𝓝 (∫ r in Ioi 0, ouScoreEnergy n ν r)) := by
  let I := ouScoreEnergy n ν
  let σ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℝ := fun k => (Ioi (((k : ℝ) + 1)⁻¹)).indicator I
  have hI : Integrable I σ := ouScoreEnergy_integrable_Ioi n ν hxi v hv hweak
  have hFm (k : ℕ) : AEStronglyMeasurable (F k) σ := hI.aestronglyMeasurable.indicator measurableSet_Ioi
  have hFb (k : ℕ) : ∀ᵐ r ∂σ, ‖F k r‖ ≤ ‖I r‖ := by
    exact Filter.Eventually.of_forall fun r => by
      by_cases hr : r ∈ Ioi (((k : ℝ) + 1)⁻¹)
      · simp only [F, indicator_of_mem hr, le_refl]
      · simp only [F, indicator_of_notMem hr, norm_zero, norm_nonneg]
  have hpoint : ∀ᵐ r ∂σ, Tendsto (fun k => F k r) atTop (𝓝 (I r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    change 0 < r at hr
    have hsmall : ∀ᶠ k : ℕ in atTop, ((k : ℝ) + 1)⁻¹ < r :=
      tendsto_inverse_succ.eventually (gt_mem_nhds hr)
    have heq : (fun k => F k r) =ᶠ[atTop] (fun _ => I r) := hsmall.mono fun k hk =>
      indicator_of_mem hk I
    exact tendsto_const_nhds.congr' heq.symm
  have h := tendsto_integral_of_dominated_convergence (fun r => ‖I r‖) hFm hI.norm hFb hpoint
  have heq (k : ℕ) : (∫ r, F k r ∂σ) = ∫ r in Ioi (((k : ℝ) + 1)⁻¹), I r := by
    rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    rw [inter_eq_left.mpr (show Ioi (((k : ℝ) + 1)⁻¹) ⊆ Ioi (0 : ℝ) from
      fun r hr => (by positivity : (0 : ℝ) < ((k : ℝ) + 1)⁻¹).trans hr)]
  simpa only [heq] using h

theorem ou_entropy_dissipation_global (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ volume)
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) :
    klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    IntegrableOn (ouScoreEnergy n ν) (Ioi 0) volume ∧
    klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal (∫ r in Ioi 0, ouScoreEnergy n ν r) ∧
    (klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal =
      ∫ r in Ioi 0, ouScoreEnergy n ν r := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let a : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  have ha (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have hfin : klDiv ν γ ≠ ∞ := (ou_initial_entropy_bound n ν hac hxi v hv hweak).2
  have ha0 : Tendsto a atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_inverse_succ, Filter.Eventually.of_forall ha⟩
  have hE := (ouInitial_entropy_tendsto_of_volume_ac n ν hac).comp ha0
  have hReal : Tendsto (fun k => (klDiv (ouInitialLaw n ν (a k)) γ).toReal) atTop
      (𝓝 (klDiv ν γ).toReal) := by
    simpa only [γ, Function.comp_def] using!
      (ENNReal.continuousAt_toReal hfin).tendsto.comp hE
  have htail := ou_score_tail_tendsto_zero_sequence n ν hxi v hv hweak
  have hEq : (fun k => (klDiv (ouInitialLaw n ν (a k)) γ).toReal) =ᶠ[atTop]
      (fun k => ∫ r in Ioi (a k), ouScoreEnergy n ν r) :=
    Filter.Eventually.of_forall fun k => ou_positive_entropy_eq_score_tail n ν hxi v hv hweak (a k) (ha k)
  have hFull : (klDiv ν γ).toReal = ∫ r in Ioi 0, ouScoreEnergy n ν r :=
    tendsto_nhds_unique hReal (htail.congr' hEq.symm)
  refine ⟨hfin, ouScoreEnergy_integrable_Ioi n ν hxi v hv hweak, ?_, hFull⟩
  calc
    klDiv ν γ = ENNReal.ofReal (klDiv ν γ).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ = _ := congrArg ENNReal.ofReal hFull

end AffineFKProof
