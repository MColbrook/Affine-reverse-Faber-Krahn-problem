module

public import AffineFK.ConditionalSteinPairing

/-!
# Conditional tensor representation preserves the Hessian contraction

Every coordinate is paired with its genuine compact smooth second partial.
The finite sums pass through the integrals using the coordinate integrability
proved by the conditional pairing theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem conditional_tensor_contraction_pairing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (W : Ω → EuclideanSpace ℝ (Fin n)) (hW : Measurable W)
    (A : Ω → EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (hA : MemLp A 2 μ)
    (Tm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (c : ℝ)
    (hrep : ∀ ω, Tm (W ω) = c •
      condExp ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W) μ A ω)
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun ω => tensorPartialContraction n Tm i φ (W ω)) μ ∧
    Integrable (fun ω => ∑ j : Fin n, ∑ k : Fin n,
      A ω (i, j, k) * partialTest n k (partialTest n j φ) (W ω)) μ ∧
    (∫ ω, tensorPartialContraction n Tm i φ (W ω) ∂μ) =
      c * (∫ ω, ∑ j : Fin n, ∑ k : Fin n,
        A ω (i, j, k) * partialTest n k (partialTest n j φ) (W ω) ∂μ) := by
  let L : Fin n → Fin n → Ω → ℝ := fun j k ω =>
    Tm (W ω) (i, j, k) * partialTest n k (partialTest n j φ) (W ω)
  let R : Fin n → Fin n → Ω → ℝ := fun j k ω =>
    A ω (i, j, k) * partialTest n k (partialTest n j φ) (W ω)
  have hp (j k : Fin n) : Integrable (L j k) μ ∧
      (∫ ω, L j k ω ∂μ) = c * (∫ ω, R j k ω ∂μ) :=
    conditional_tensor_representation_pairing μ n W hW A hA Tm c hrep (i, j, k)
      (partialTest n k (partialTest n j φ))
  have hR (j k : Fin n) : Integrable (R j k) μ :=
    tensor_coordinate_test_pairing_integrable μ n W hW A hA (i, j, k)
      (partialTest n k (partialTest n j φ))
  have hLJ (j : Fin n) : Integrable (fun ω => ∑ k, L j k ω) μ :=
    integrable_finsetSum Finset.univ (fun k _hk => (hp j k).1)
  have hRJ (j : Fin n) : Integrable (fun ω => ∑ k, R j k ω) μ :=
    integrable_finsetSum Finset.univ (fun k _hk => hR j k)
  have hLI : (∫ ω, ∑ j, ∑ k, L j k ω ∂μ) = ∑ j, ∑ k, ∫ ω, L j k ω ∂μ := by
    rw [integral_finsetSum Finset.univ (fun j _hj => hLJ j)]
    apply Finset.sum_congr rfl
    intro j _hj
    exact integral_finsetSum Finset.univ (fun k _hk => (hp j k).1)
  have hRI : (∫ ω, ∑ j, ∑ k, R j k ω ∂μ) = ∑ j, ∑ k, ∫ ω, R j k ω ∂μ := by
    rw [integral_finsetSum Finset.univ (fun j _hj => hRJ j)]
    apply Finset.sum_congr rfl
    intro j _hj
    exact integral_finsetSum Finset.univ (fun k _hk => hR j k)
  refine ⟨?_, integrable_finsetSum Finset.univ (fun j _hj => hRJ j), ?_⟩
  · change Integrable (fun ω => ∑ j, ∑ k, L j k ω) μ
    exact integrable_finsetSum Finset.univ (fun j _hj => hLJ j)
  · change (∫ ω, ∑ j, ∑ k, L j k ω ∂μ) = c * (∫ ω, ∑ j, ∑ k, R j k ω ∂μ)
    rw [hLI, hRI]
    have hEq (j k : Fin n) : (∫ ω, L j k ω ∂μ) = c * (∫ ω, R j k ω ∂μ) := (hp j k).2
    simp_rw [hEq, ← Finset.mul_sum]

end AffineFKProof
