module

public import AffineFK.RandomGaussianTensorMoment
public import AffineFK.ConditionalVectorField

/-!
# Conditional representation of the quadratic Gaussian contraction

This is the conditioning and energy step of the smoothing argument. The
field has not yet been identified with a logarithmic relative score.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem gaussian_hermite_conditional_field
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (a b c : ℝ) :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧
      MemLp r 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        r (a • p.1 + b • p.2) = c • condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • q.1 + b • q.2))
          (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
          (fun q => gaussianHermiteContraction n (T q.1) q.2) p) ∧
      (∫ x, ‖r x‖ ^ 2 ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ≤ 2 * c ^ 2 * (∫ u, ‖T u‖ ^ 2 ∂ν) ∧
      ∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        StronglyMeasurable F →
        MemLp F 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) →
        Integrable (fun x => ⟪r x, F x⟫)
          ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) ∧
        Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ⟪gaussianHermiteContraction n (T p.1) p.2, F (a • p.1 + b • p.2)⟫)
          (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
        (∫ x, ⟪r x, F x⟫ ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) =
          c * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
            ⟪gaussianHermiteContraction n (T p.1) p.2, F (a • p.1 + b • p.2)⟫
            ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  have hQ := random_gaussian_tensor_hermite_contraction n ν T hT
  obtain ⟨r, hr, hrLp, hrep, hbound, hpair⟩ := scaled_conditional_vector_field
    (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) n
    (fun p => gaussianHermiteContraction n (T p.1) p.2) hQ.1
    (fun p => a • p.1 + b • p.2) (by fun_prop) c
  refine ⟨r, hr, hrLp, hrep, ?_, hpair⟩
  calc
    _ ≤ c ^ 2 * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖gaussianHermiteContraction n (T p.1) p.2‖ ^ 2
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := hbound
    _ ≤ c ^ 2 * (2 * (∫ u, ‖T u‖ ^ 2 ∂ν)) := mul_le_mul_of_nonneg_left hQ.2.2 (sq_nonneg c)
    _ = _ := by ring

end AffineFKProof
