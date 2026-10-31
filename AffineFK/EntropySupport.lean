module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Tactic.Linarith

/-!
# Entropy and support

This module formalises the manuscript's entropy--support lemma for genuine
probability measures. Entropy is Mathlib's extended-valued Kullback--Leibler
divergence; a real-valued entropy is used only under an explicit finiteness
hypothesis.

Reused formal proofs: the Radon--Nikodym chain rule and restriction theorems,
by the Mathlib measure-theory contributors, and the Gibbs/normalisation
inequality in KullbackLeibler.Basic, by Rémy Degenne and Lorenzo Luccioli.
All library material retains its Apache-2.0 attribution.
-/

public section
namespace AffineFKProof
open MeasureTheory Set InformationTheory
open scoped ENNReal

/-- Restricting the reference measure to a set carrying the entire first measure
does not change its log-likelihood ratio almost everywhere. -/
theorem llr_restrict_reference_of_ae_mem
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set α) (hA : MeasurableSet A)
    (hmem : ∀ᵐ x ∂μ, x ∈ A) (hac : μ ≪ ν) :
    llr μ (ν.restrict A) =ᵐ[μ] llr μ ν := by
  have hacA : μ ≪ ν.restrict A := by
    have h := hac.restrict A
    rwa [Measure.restrict_eq_self_of_ae_mem hmem] at h
  have hchain := hacA.ae_le
    (Measure.rnDeriv_mul_rnDeriv' (μ := μ) (ν := ν.restrict A)
      (κ := ν) Measure.absolutelyContinuous_restrict)
  have hind := hac.ae_le (Measure.rnDeriv_restrict_self ν hA)
  filter_upwards [hchain, hind, hmem] with x hx hi hm
  simp only [Pi.mul_apply, Set.indicator_of_mem hm, Pi.one_apply] at hx hi
  simp only [llr, hi, mul_one] at hx ⊢
  rw [hx]

/-- The finite-entropy form of the manuscript's support estimate. No absolute
continuity or integrability premise is left undischarged: both follow from
finite Kullback--Leibler divergence. -/
theorem entropy_support_finite
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) (hA : MeasurableSet A)
    (hmem : ∀ᵐ x ∂μ, x ∈ A)
    (hfinite : klDiv μ ν ≠ ∞) :
    -Real.log (ν.real A) ≤ (klDiv μ ν).toReal := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hfinite
  have hacA : μ ≪ ν.restrict A := by
    have h := hac.restrict A
    rwa [Measure.restrict_eq_self_of_ae_mem hmem] at h
  have heq := llr_restrict_reference_of_ae_mem μ ν A hA hmem hac
  have hintA : Integrable (llr μ (ν.restrict A)) μ :=
    hint.congr heq.symm
  have hg := integral_llr_add_mul_log_nonneg hacA hintA
  have hi : ∫ x, llr μ (ν.restrict A) x ∂μ = ∫ x, llr μ ν x ∂μ :=
    integral_congr_ae heq
  rw [hi] at hg
  rw [toReal_klDiv hac hint]
  simp only [measureReal_def, Measure.restrict_apply_univ, measure_univ,
    ENNReal.toReal_one, one_mul, add_sub_cancel_right] at hg ⊢
  linarith

/-- The entropy--support inequality, including infinite entropy. For positive
reference mass this is exactly the negative logarithm in the manuscript.
At zero reference mass, Lean's log-zero convention makes this bound trivial;
the null-support theorem below gives the infinite-entropy conclusion. -/
theorem entropy_support
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) (hA : MeasurableSet A)
    (hmem : ∀ᵐ x ∂μ, x ∈ A) :
    ENNReal.ofReal (-Real.log (ν.real A)) ≤ klDiv μ ν := by
  by_cases hfinite : klDiv μ ν = ∞
  · simp only [hfinite, le_top]
  · rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal (entropy_support_finite μ ν A hA hmem hfinite)

/-- A probability measure carried by a reference-null set has infinite entropy.
This assertion also covers singular probability measures. -/
theorem entropy_support_null
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) (hA : MeasurableSet A)
    (hmem : ∀ᵐ x ∂μ, x ∈ A) (hnull : ν A = 0) :
    klDiv μ ν = ∞ := by
  apply klDiv_of_not_ac
  intro hac
  have hzero : μ A = 0 := hac hnull
  have hfull : μ A = μ univ :=
    (ae_mem_iff_measure_eq hA.nullMeasurableSet).mp hmem
  simp only [hfull, measure_univ, one_ne_zero] at hzero

/-- An extended-valued version with the correct infinite support cost at zero
reference mass. For positive Gaussian mass its conclusion is the manuscript's
entropy--support inequality. -/
theorem entropy_support_extended
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) (hA : MeasurableSet A)
    (hmem : ∀ᵐ x ∂μ, x ∈ A) :
    (if ν A = 0 then ∞ else ENNReal.ofReal (-Real.log (ν.real A))) ≤
      klDiv μ ν := by
  by_cases hnull : ν A = 0
  · rw [ite_eq_left hnull, entropy_support_null μ ν A hA hmem hnull]
  · rw [ite_eq_right hnull]
    exact entropy_support μ ν A hA hmem

/-- The conditioned-entropy identity in the source proof. Conditioning the
reference measure on a positive-mass support preserves finite entropy and
subtracts the negative logarithm of the reference mass. -/
theorem entropy_conditioned_identity
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set α) (hA : MeasurableSet A)
    (hmem : ∀ᵐ x ∂μ, x ∈ A) (hpos : ν A ≠ 0)
    (hfinite : klDiv μ ν ≠ ∞) :
    klDiv μ (ProbabilityTheory.cond ν A) ≠ ∞ ∧
      (klDiv μ ν).toReal =
        (klDiv μ (ProbabilityTheory.cond ν A)).toReal - Real.log (ν.real A) := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hfinite
  have hacA : μ ≪ ν.restrict A := by
    have h := hac.restrict A
    rwa [Measure.restrict_eq_self_of_ae_mem hmem] at h
  have hc0 : (ν A)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top ν A)
  have hctop : (ν A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hpos
  have hllr : llr μ (ProbabilityTheory.cond ν A) =ᵐ[μ]
      (fun x => llr μ ν x + Real.log (ν.real A)) := by
    filter_upwards [llr_smul_right hacA (ν A)⁻¹ hc0 hctop,
      llr_restrict_reference_of_ae_mem μ ν A hA hmem hac] with x hx hr
    simpa only [ProbabilityTheory.cond, hr, ENNReal.toReal_inv, Real.log_inv,
      sub_neg_eq_add, measureReal_def] using hx
  have haccond : μ ≪ ProbabilityTheory.cond ν A := hacA.smul_right hc0
  have hintcond : Integrable (llr μ (ProbabilityTheory.cond ν A)) μ :=
    (hint.add (integrable_const _)).congr hllr.symm
  have : IsProbabilityMeasure (ProbabilityTheory.cond ν A) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos
  refine ⟨klDiv_ne_top_iff.mpr ⟨haccond, hintcond⟩, ?_⟩
  rw [toReal_klDiv hac hint, toReal_klDiv haccond hintcond,
    integral_congr_ae hllr, integral_add hint (integrable_const _), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul, add_sub_cancel_right]

end AffineFKProof
