module

public import AffineFK.SmoothedHermiteComponent
public import AffineFK.SteinIdentityComponents

/-!
# Vector-field identities under Gaussian smoothing

The original vector Stein identity yields its genuine scalar components.
Finite sums then give the actual smoothed vector identity with exact a³
and a³/b² factors. The Hessian order agrees with vectorHessianContraction;
Schwarz symmetry of smooth test functions supplies the component order.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

def smoothedVectorHessianContraction (n : ℕ)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)))
    (a b : ℝ) (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    T p.1 (i, j, k) * partialTest n j (partialTest n k (vectorComponentTest n i F)) (a • p.1 + b • p.2)

theorem smoothedVectorHessianContraction_components (n : ℕ)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)))
    (a b : ℝ) (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    smoothedVectorHessianContraction n T F a b p =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j (vectorComponentTest n i F)) (a • p.1 + b • p.2) := by
  unfold smoothedVectorHessianContraction
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [partialTest_commute n j k]

theorem smoothed_stein_vector_identities
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) = ∫ x, vectorHessianContraction n T F x ∂ν)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n))) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪a • p.1 + b • p.2, F (a • p.1 + b • p.2)⟫ - vectorDivergence n F (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (smoothedVectorHessianContraction n T F a b)
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪gaussianHermiteContraction n (T p.1) p.2, F (a • p.1 + b • p.2)⟫)
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p, ⟪a • p.1 + b • p.2, F (a • p.1 + b • p.2)⟫ - vectorDivergence n F (a • p.1 + b • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      a ^ 3 * (∫ p, smoothedVectorHessianContraction n T F a b p
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p, ⟪a • p.1 + b • p.2, F (a • p.1 + b • p.2)⟫ - vectorDivergence n F (a • p.1 + b • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      (a ^ 3 / b ^ 2) * (∫ p, ⟪gaussianHermiteContraction n (T p.1) p.2, F (a • p.1 + b • p.2)⟫
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let μ := ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))
  let Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hcomp := vector_identity_implies_component_identity n ν hxi T hidentity
  have hraw (i : Fin n) := smoothed_stein_component_identity n ν T hT i (hxi i) (hcomp i)
    a b ha hb hab (vectorComponentTest n i F)
  have hherm (i : Fin n) := smoothed_hermite_component_identity n ν T hT i (hxi i) (hcomp i)
    a b ha hb hab (vectorComponentTest n i F)
  have hl (i : Fin n) : Integrable (fun p =>
      Φ p i * vectorComponentTest n i F (Φ p) - partialTest n i (vectorComponentTest n i F) (Φ p)) μ :=
    (hraw i).1.sub (hraw i).2.1
  have hh (i : Fin n) : Integrable (fun p => ∑ j : Fin n, ∑ k : Fin n,
      T p.1 (i, j, k) * partialTest n k (partialTest n j (vectorComponentTest n i F)) (Φ p)) μ :=
    (hraw i).2.2.1
  have hr (i : Fin n) : Integrable (fun p =>
      gaussianHermiteContraction n (T p.1) p.2 i * vectorComponentTest n i F (Φ p)) μ := (hherm i).1
  have hleft : (fun p => ⟪Φ p, F (Φ p)⟫ - vectorDivergence n F (Φ p)) =
      (fun p => ∑ i : Fin n,
        (Φ p i * vectorComponentTest n i F (Φ p) - partialTest n i (vectorComponentTest n i F) (Φ p))) :=
    funext fun p => vector_stein_left_sum n F (Φ p)
  have hhess : smoothedVectorHessianContraction n T F a b =
      (fun p => ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j (vectorComponentTest n i F)) (Φ p)) :=
    funext (smoothedVectorHessianContraction_components n T F a b)
  have hright : (fun p => ⟪gaussianHermiteContraction n (T p.1) p.2, F (Φ p)⟫) =
      (fun p => ∑ i : Fin n, gaussianHermiteContraction n (T p.1) p.2 i * vectorComponentTest n i F (Φ p)) := by
    funext p
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, vectorComponentTest_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hleft]
    exact integrable_finsetSum _ fun i _ => hl i
  · rw [hhess]
    exact integrable_finsetSum _ fun i _ => hh i
  · rw [hright]
    exact integrable_finsetSum _ fun i _ => hr i
  · rw [hleft, integral_finsetSum _ fun i _ => hl i, hhess,
      integral_finsetSum _ fun i _ => hh i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_sub (hraw i).1 (hraw i).2.1]
    exact (hraw i).2.2.2
  · rw [hleft, integral_finsetSum _ fun i _ => hl i, hright,
      integral_finsetSum _ fun i _ => hr i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_sub (hraw i).1 (hraw i).2.1]
    exact (hherm i).2

end AffineFKProof
