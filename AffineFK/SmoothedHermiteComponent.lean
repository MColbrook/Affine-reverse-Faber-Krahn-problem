module

public import AffineFK.SmoothedSteinComponent
public import AffineFK.WeightedGaussianSmoothing
public import AffineFK.GaussianTensorContraction

/-!
# The smoothed Hermite compact-test identity

The two Gaussian integrations by parts replace the genuine Hessian
contraction by A:(GGᵀ-Id), with the exact factor a³/b². Every weighted
integrand is proved integrable before the finite sums and integrals
are interchanged. The relative logarithmic score and conditioning are
not premises or conclusions of this compact-test lemma.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

theorem smoothed_hermite_component_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, x i * ψ x ∂ν) - (∫ x, partialTest n i ψ x ∂ν) =
        ∫ x, tensorPartialContraction n T i ψ x ∂ν)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      gaussianHermiteContraction n (T p.1) p.2 i * φ (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p, (a • p.1 + b • p.2) i * φ (a • p.1 + b • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) -
      (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      (a ^ 3 / b ^ 2) * (∫ p, gaussianHermiteContraction n (T p.1) p.2 i * φ (a • p.1 + b • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let R : Fin n → Fin n → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun j k p => (T p.1 (i, j, k) * (p.2 j * p.2 k - if j = k then 1 else 0)) * φ (a • p.1 + b • p.2)
  let L : Fin n → Fin n → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun j k p => T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2)
  have hW (j k : Fin n) := product_gaussian_weighted_second_integration_by_parts n ν T hT i j k a b hb φ
  have hR (j k : Fin n) : Integrable (R j k) (ν.prod γ) := (hW j k).2.1
  have hL (j k : Fin n) : Integrable (L j k) (ν.prod γ) := (hW j k).1
  have hRrow (j : Fin n) : Integrable (fun p => ∑ k, R j k p) (ν.prod γ) :=
    integrable_finsetSum _ fun k _ => hR j k
  have hLrow (j : Fin n) : Integrable (fun p => ∑ k, L j k p) (ν.prod γ) :=
    integrable_finsetSum _ fun k _ => hL j k
  have hrows (j : Fin n) : (∫ p, ∑ k, R j k p ∂ν.prod γ) =
      b ^ 2 * (∫ p, ∑ k, L j k p ∂ν.prod γ) := by
    rw [integral_finsetSum _ fun k _ => hR j k,
      integral_finsetSum _ fun k _ => hL j k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (hW j k).2.2
  have hsum : (∫ p, ∑ j, ∑ k, R j k p ∂ν.prod γ) =
      b ^ 2 * (∫ p, ∑ j, ∑ k, L j k p ∂ν.prod γ) := by
    rw [integral_finsetSum _ fun j _ => hRrow j,
      integral_finsetSum _ fun j _ => hLrow j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hrows j
  have hQ : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      gaussianHermiteContraction n (T p.1) p.2 i * φ (a • p.1 + b • p.2)) =
      (fun p => ∑ j, ∑ k, R j k p) := by
    funext p
    change (∑ j : Fin n, ∑ k : Fin n,
      T p.1 (i, j, k) * (p.2 j * p.2 k - if j = k then 1 else 0)) * φ (a • p.1 + b • p.2) = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_mul _ _ _
  have hQsum : (∫ p, gaussianHermiteContraction n (T p.1) p.2 i * φ (a • p.1 + b • p.2) ∂ν.prod γ) =
      b ^ 2 * (∫ p, ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2) ∂ν.prod γ) := by
    rw [hQ]
    exact hsum
  refine ⟨?_, ?_⟩
  · rw [hQ]
    exact integrable_finsetSum _ fun j _ => hRrow j
  · calc
      _ = a ^ 3 * (∫ p, ∑ j : Fin n, ∑ k : Fin n,
          T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2) ∂ν.prod γ) :=
        (smoothed_stein_component_identity n ν T hT i hxi hidentity a b ha hb hab φ).2.2.2
      _ = (a ^ 3 / b ^ 2) * (b ^ 2 * (∫ p, ∑ j : Fin n, ∑ k : Fin n,
          T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (a • p.1 + b • p.2) ∂ν.prod γ)) := by
        field_simp [hb]
      _ = _ := by rw [hQsum]

end AffineFKProof
