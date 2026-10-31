module

public import AffineFK.OUEntropyContraction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convergence of the actual OU laws to the original probability measure

Bounded continuous tests converge by a single product-space coupling and
Mathlib's dominated convergence theorem. No moment hypothesis is needed.
The DCT and weak-probability topology results retain their Mathlib attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

theorem ouInitial_coupling_tendsto (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ => Real.exp (-t) • p.1 +
      Real.sqrt (1 - Real.exp (-2 * t)) • p.2) (𝓝 0) (𝓝 p.1) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-t) • p.1 +
      Real.sqrt (1 - Real.exp (-2 * t)) • p.2) := by fun_prop
  simpa using hc.continuousAt.tendsto (x := 0)

theorem ouInitial_integral_boundedContinuous_tendsto (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (f : EuclideanSpace ℝ (Fin n) →ᵇ ℝ) :
    Tendsto (fun t => ∫ x, f x ∂ouInitialLaw n ν t) (𝓝 0) (𝓝 (∫ x, f x ∂ν)) := by
  have hi : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), f p.1
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) = ∫ x, f x ∂ν := by
    rw [integral_fun_fst]
    simp
  have h := tendsto_integral_filter_of_norm_le_const
    (μ := ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
    (l := 𝓝 (0 : ℝ))
    (F := fun t p => f (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2))
    (f := fun p => f p.1)
    (Filter.Eventually.of_forall fun t =>
      (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
    ⟨‖f‖, Filter.Eventually.of_forall fun t =>
      Filter.Eventually.of_forall fun p => f.norm_coe_le_norm _⟩
    (Filter.Eventually.of_forall fun p =>
      f.continuous.continuousAt.tendsto.comp (ouInitial_coupling_tendsto n p))
  rw [hi] at h
  convert h using 1
  ext t
  exact integral_map (by fun_prop) (by fun_prop)

def ouInitialProbability (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (t : ℝ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
  ⟨ouInitialLaw n ν t, by unfold ouInitialLaw; infer_instance⟩

theorem ouInitial_probability_tendsto (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] :
    Tendsto (ouInitialProbability n ν) (𝓝 0)
      (𝓝 (⟨ν, inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  exact ouInitial_integral_boundedContinuous_tendsto n ν

end AffineFKProof
