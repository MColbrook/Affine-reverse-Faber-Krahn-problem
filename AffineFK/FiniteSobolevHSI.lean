module

public import AffineFK.OUFiniteSobolevInformation
public import AffineFK.OUEntropyDissipationGlobal
public import AffineFK.OUInformationIntegralGlobal

/-!
# Entropy from a genuine second-order Stein tensor on the Sobolev domain

The initial square root belongs to the actual unweighted H1 completion.
Its weak relative score is derived from that hypothesis. The full entropy
identity and both positive-time information bounds have already been
proved for the actual OU law. Integrating their minimum gives the exact
sqrt(2) constant. Initial entropy finiteness is a conclusion.

This is the second-order entropy--Stein--information method of Ledoux,
Nourdin and Peccati, with the manuscript's second-order tensor estimate.
The imported modules retain attribution for the reused Mathlib proofs.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Set
open scoped Distributions RealInnerProductSpace ENNReal

theorem finiteSobolev_second_order_HSI (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x))
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ))
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 (densityMeasure n ρ))
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ) =
        ∫ x, vectorHessianContraction n T F x ∂densityMeasure n ρ) :
    let I : ℝ := ∫ x, ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2
    let S : ℝ := ∫ x, ‖T x‖ ^ 2 ∂densityMeasure n ρ
    Integrable (fun x => ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    klDiv (densityMeasure n ρ) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    IntegrableOn (ouScoreEnergy n (densityMeasure n ρ)) (Ioi 0) volume ∧
    klDiv (densityMeasure n ρ) (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal (∫ t in Ioi 0, ouScoreEnergy n (densityMeasure n ρ) t) ∧
    klDiv (densityMeasure n ρ) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (Real.sqrt 2 * Real.sqrt S * Real.sqrt I) := by
  dsimp only
  let ν := densityMeasure n ρ
  let I : ℝ := ∫ x, ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2
  let S : ℝ := ∫ x, ‖T x‖ ^ 2 ∂ν
  have hI : 0 ≤ I := integral_nonneg (fun x => sq_nonneg _)
  have hS : 0 ≤ S := integral_nonneg (fun x => sq_nonneg _)
  obtain ⟨s, _, hs, _, hL1, _, hweak⟩ :=
    finiteSobolev_density_relative_score n ρ hρ0 v hv hsecond
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr hsecond
  have hxi (i : Fin n) : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν := hX.eval_piLp i
  have hac : ν ≪ volume := withDensity_absolutelyContinuous _ _
  have hglobal := ou_entropy_dissipation_global n ν hac hxi s hs (fun F => (hweak F).2.2)
  have hdom := ouInformationEnvelope_integrable_Ioi I S hI hS
  have hint : (∫ t in Ioi 0, ouScoreEnergy n ν t) ≤
      ∫ t in Ioi 0, ouInformationEnvelope I S t := by
    apply integral_mono_ae hglobal.2.1 hdom
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hbound := (finiteSobolev_OU_two_score_bounds n ρ hρ0 v hv hsecond T hT hidentity t ht).2.2
    simpa only [ouScoreEnergy, ouInitialLaw, ouInformationEnvelope, I, S, ν] using hbound
  refine ⟨hL1, hglobal.1, hglobal.2.1, hglobal.2.2.1, ?_⟩
  rw [hglobal.2.2.1]
  exact ENNReal.ofReal_le_ofReal (hint.trans (ouInformationEnvelope_integral_Ioi_bound I S hI hS))

end AffineFKProof
