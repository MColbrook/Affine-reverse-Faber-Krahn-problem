module

public import AffineFK.FirstOrderSmoothingComponent

/-!
# The actual first-order vector identity on the smoothing product space

One-coordinate compact tests and the proved first-order scalar smoothing
identity are summed only after every summand has been proved integrable.
The same original square-integrable field is evaluated at the first input.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem firstOrder_smoothed_vector_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪s x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n))) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪a • p.1 + b • p.2, F (a • p.1 + b • p.2)⟫ - vectorDivergence n F (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪s p.1, F (a • p.1 + b • p.2)⟫)
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p, ⟪a • p.1 + b • p.2, F (a • p.1 + b • p.2)⟫ - vectorDivergence n F (a • p.1 + b • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      a * (∫ p, ⟪s p.1, F (a • p.1 + b • p.2)⟫
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let μ := ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hcomp (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
      (∫ x, s x i * φ x ∂ν) = (∫ x, x i * φ x ∂ν) - ∫ x, partialTest n i φ x ∂ν :=
    (firstOrder_source_component_identity n ν hxi s hs hweak i φ).2.2.2
  have hraw (i : Fin n) := firstOrder_smoothed_component_identity n ν s hs i (hxi i)
    (hcomp i) a b ha hb hab (vectorComponentTest n i F)
  have hl (i : Fin n) : Integrable (fun p => W p i * vectorComponentTest n i F (W p) -
      partialTest n i (vectorComponentTest n i F) (W p)) μ :=
    (hraw i).1.sub (hraw i).2.1
  have hr (i : Fin n) : Integrable (fun p => s p.1 i * vectorComponentTest n i F (W p)) μ :=
    (hraw i).2.2.1
  have hleft : (fun p => ⟪W p, F (W p)⟫ - vectorDivergence n F (W p)) =
      (fun p => ∑ i : Fin n,
        (W p i * vectorComponentTest n i F (W p) - partialTest n i (vectorComponentTest n i F) (W p))) :=
    funext fun p => vector_stein_left_sum n F (W p)
  have hright : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪s p.1, F (W p)⟫) =
      (fun p => ∑ i : Fin n, s p.1 i * vectorComponentTest n i F (W p)) := by
    funext p
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, vectorComponentTest_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact integrable_finsetSum _ fun i _ => hl i
  · rw [hright]
    exact integrable_finsetSum _ fun i _ => hr i
  · rw [hleft, integral_finsetSum _ fun i _ => hl i, hright,
      integral_finsetSum _ fun i _ => hr i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_sub (hraw i).1 (hraw i).2.1]
    exact (hraw i).2.2.2

end AffineFKProof
