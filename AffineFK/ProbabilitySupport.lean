module

public import AffineFK.Geometry
public import AffineFK.EntropySupport
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Probability support of normalised sums

These statements supply the actual almost-everywhere and push-forward support
steps used after the entropy estimate for sums. Independence is unnecessary for
support containment, so the assertions apply to arbitrary jointly defined random
vectors with the stated marginal support. They do not assert entropy decay.

The proofs reuse Mathlib's finite-filter conjunction, measurable finite sums,
push-forward probability and almost-everywhere transfer, and standard Gaussian
probability instance. The source headers identify the library contributors.
-/

public section
namespace AffineFKProof
open MeasureTheory Set InformationTheory
open scoped BigOperators Pointwise ENNReal

/-- The almost-everywhere support statement behind the square-root dilation. -/
theorem ae_normalized_sum_mem_sqrt_dilate
    {Ω E : Type*} [MeasurableSpace Ω] [AddCommGroup E] [Module ℝ E]
    (μ : Measure Ω) (D : Set E) (hD : Convex ℝ D)
    (m : ℕ) (hm : 0 < m) (U : Fin m → Ω → E)
    (hsupport : ∀ i, ∀ᵐ ω ∂μ, U i ω ∈ D) :
    ∀ᵐ ω ∂μ, (Real.sqrt (m : ℝ))⁻¹ • (∑ i, U i ω) ∈
      (Real.sqrt (m : ℝ)) • D := by
  filter_upwards [Filter.eventually_all.mpr hsupport] with ω hω
  exact normalized_sum_mem_sqrt_dilate hD hm (fun i => U i ω) hω

/-- The law of a normalised finite sum is a probability measure carried by the
square-root dilation of the compact convex marginal support. -/
theorem normalized_sum_law_support
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Set E) (hcompact : IsCompact D) (hD : Convex ℝ D)
    (m : ℕ) (hm : 0 < m) (U : Fin m → Ω → E)
    (hmeas : ∀ i, AEMeasurable (U i) μ)
    (hsupport : ∀ i, ∀ᵐ ω ∂μ, U i ω ∈ D) :
    IsProbabilityMeasure
      (μ.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ • (∑ i, U i ω))) ∧
    ∀ᵐ z ∂μ.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ • (∑ i, U i ω)),
      z ∈ (Real.sqrt (m : ℝ)) • D := by
  have hW : AEMeasurable
      (fun ω => (Real.sqrt (m : ℝ))⁻¹ • (∑ i, U i ω)) μ := by
    exact (Finset.aemeasurable_fun_sum Finset.univ (fun i _hi => hmeas i)).const_smul _
  have hset : MeasurableSet ((Real.sqrt (m : ℝ)) • D) :=
    (hcompact.image (continuous_const_smul (Real.sqrt (m : ℝ)))).measurableSet
  refine ⟨(Measure.isProbabilityMeasure_map_iff hW).mpr inferInstance, ?_⟩
  exact (ae_map_iff hW hset).mpr
    (ae_normalized_sum_mem_sqrt_dilate μ D hD m hm U hsupport)

/-- Applying the source's entropy--support inequality to the actual law of a
normalised sum. The piecewise left side preserves infinite cost at zero Gaussian
mass; in the manuscript's positive-mass setting it is the usual negative log. -/
theorem gaussian_entropy_of_normalized_sum_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact D) (hD : Convex ℝ D)
    (m : ℕ) (hm : 0 < m) (U : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hmeas : ∀ i, AEMeasurable (U i) μ)
    (hsupport : ∀ i, ∀ᵐ ω ∂μ, U i ω ∈ D) :
    (if ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))
        ((Real.sqrt (m : ℝ)) • D) = 0
      then ∞
      else ENNReal.ofReal
        (-Real.log ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).real
          ((Real.sqrt (m : ℝ)) • D)))) ≤
      klDiv (μ.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ • (∑ i, U i ω)))
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨hlaw, hsupp⟩ :=
    normalized_sum_law_support μ D hcompact hD m hm U hmeas hsupport
  have : IsProbabilityMeasure
      (μ.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ • (∑ i, U i ω))) := hlaw
  exact entropy_support_extended _ _ _
    (hcompact.image (continuous_const_smul (Real.sqrt (m : ℝ)))).measurableSet hsupp

end AffineFKProof
