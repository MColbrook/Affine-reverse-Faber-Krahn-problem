module

public import AffineFK.OUEntropyDissipationScalarLimit
public import AffineFK.EntropyTruncationConvergence

/-!
# Actual positive-time OU entropy dissipation

The explicit scalar truncation sequence removes the last intermediate
convergence premises. Entropy is the actual extended-valued KL divergence
of the actual smoothed image law, and information is the squared norm of
the actual logarithmic Gaussian-relative score. Both entropy finiteness
and time integrability of information are conclusions. The original input
has L2 coordinates and a genuine L2 weak relative score; no initial smooth
density, entropy derivative, finite initial entropy, LSI or dissipation
identity is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace Topology Interval ENNReal

theorem ou_entropy_dissipation (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
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
  apply ou_entropy_dissipation_of_scalar_limits n ν hxi v hv hweak
    (fun k : ℕ => ((k : ℝ) + 1)⁻¹) (fun k : ℕ => (k : ℝ) + 1)
    (fun k => (entropyTruncationSequence_domain k).1)
    (fun k => (entropyTruncationSequence_domain k).2)
  · intro r hr
    simpa only [entropyTruncationSequence] using entropyTruncationSequence_tendsto r hr.le
  · intro r hr
    simpa only [mul_comm] using entropyTruncationSequence_fisher_weight_tendsto r hr
  · exact hs
  · exact hst

theorem ou_entropy_dissipation_ennreal (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let μ := fun r : ℝ => (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => Real.exp (-r) • p.1 + Real.sqrt (1 - Real.exp (-2 * r)) • p.2)
    let I := fun r : ℝ => ∫ x, ‖gaussianSmoothingScore n ν (Real.exp (-r))
      (Real.sqrt (1 - Real.exp (-2 * r))) x‖ ^ 2 ∂μ r
    klDiv (μ s) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    klDiv (μ t) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    IntervalIntegrable I volume s t ∧
    klDiv (μ s) (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      klDiv (μ t) (stdGaussian (EuclideanSpace ℝ (Fin n))) + ENNReal.ofReal (∫ r in s..t, I r) := by
  let μ := fun r : ℝ => (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
    (fun p => Real.exp (-r) • p.1 + Real.sqrt (1 - Real.exp (-2 * r)) • p.2)
  let I := fun r : ℝ => ∫ x, ‖gaussianSmoothingScore n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r))) x‖ ^ 2 ∂μ r
  let H := fun r : ℝ => klDiv (μ r) (stdGaussian (EuclideanSpace ℝ (Fin n)))
  have h := ou_entropy_dissipation n ν hxi v hv hweak s t hs hst
  have hnonneg : 0 ≤ ∫ r in s..t, I r :=
    intervalIntegral.integral_nonneg hst (fun r _ => integral_nonneg (fun x => sq_nonneg _))
  have hreal : (H s).toReal = (H t).toReal + ∫ r in s..t, I r := by
    have hdiff := h.2.2.2
    change (H s).toReal - (H t).toReal = ∫ r in s..t, I r at hdiff
    linarith
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  change H s = H t + ENNReal.ofReal (∫ r in s..t, I r)
  calc
    H s = ENNReal.ofReal (H s).toReal := (ENNReal.ofReal_toReal h.1).symm
    _ = ENNReal.ofReal ((H t).toReal + ∫ r in s..t, I r) := congrArg ENNReal.ofReal hreal
    _ = ENNReal.ofReal (H t).toReal + ENNReal.ofReal (∫ r in s..t, I r) :=
      ENNReal.ofReal_add ENNReal.toReal_nonneg hnonneg
    _ = _ := by rw [ENNReal.ofReal_toReal h.2.1]

end AffineFKProof
