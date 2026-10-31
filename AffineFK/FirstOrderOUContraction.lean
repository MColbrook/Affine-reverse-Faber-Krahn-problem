module

public import AffineFK.FirstOrderConditionalField
public import AffineFK.OrnsteinUhlenbeckScales

/-!
# First-order weak-field contraction at the actual OU scales

The exponential and square-root parameters are the genuine scalar
functions. The result constructs a single conditional field on their
actual image law, with energy contraction exp(-2t), before all tests.
Identification with a logarithmic relative score is separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem firstOrder_OU_conditional_vector_field
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪s x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (t : ℝ) (ht : 0 < t) :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧
      MemLp r 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        r (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2) =
          Real.exp (-t) • condExp
            ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
              (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
                Real.exp (-t) • q.1 + Real.sqrt (1 - Real.exp (-2 * t)) • q.2))
            (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) (fun q => s q.1) p) ∧
      (∫ x, ‖r x‖ ^ 2 ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ≤
        Real.exp (-2 * t) * (∫ u, ‖s u‖ ^ 2 ∂ν) ∧
      ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
        Integrable (fun x => ⟪r x, F x⟫)
          ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
            (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ∧
        Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x)
          ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
            (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ∧
        (∫ x, ⟪r x, F x⟫ ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) =
          ∫ x, ⟪x, F x⟫ - vectorDivergence n F x
            ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
              (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2) := by
  have hd := ou_smoothing_scale_domain t ht
  obtain ⟨r, hr, hrLp, hrep, hbound, htest⟩ :=
    firstOrder_smoothed_conditional_vector_field n ν hxi s hs hweak
      (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) hd.1.ne' hd.2.1.ne' hd.2.2
  refine ⟨r, hr, hrLp, hrep, ?_, htest⟩
  have hexp : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    simpa using ou_exponential_power t 2
  simpa only [hexp] using hbound

end AffineFKProof
