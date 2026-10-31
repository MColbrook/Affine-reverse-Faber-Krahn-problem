module

public import AffineFK.GroundstateLogConcaveDensity
public import AffineFK.WhiteningSpectralClosure

/-!
# The body bound from an actual log-concave groundstate representative

The weighted law's same-law strong-log-concavity representative, its
evenness, and the nonnegativity of the original H0 value are proved from
the supplied representative r. Only the existence of that original
log-concave groundstate representative and the genuine geometric
covariance lower bound remain inputs; the downstream analytic estimates
are conclusions of the existing proved chain.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal

theorem symmetric_body_eigenvalue_bound_of_logConcave_groundstate (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) (hKeven : ∀ x, -x ∈ K ↔ x ∈ K)
    (ψ : dirichletSobolev n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))))
    (hweak : IsDirichletWeakEigenfunction n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n)))
      (dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n)))).toReal ψ)
    (hψ : ψ ≠ 0)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr : Measurable r) (hr0 : ∀ x, 0 ≤ r x)
    (hrEven : ∀ x, r (-x) = r x)
    (hrlc : LogConcaveDensity (fun x => ENNReal.ofReal (r x)))
    (hrAE : r =ᵐ[volume] (dirichletValue n
      (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ψ : EuclideanSpace ℝ (Fin n) → ℝ))
    (c α : ℝ) (hc : 0 < c) (hcα : c ≤ α) (hαOne : α ≤ 1)
    (hcovX : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
      ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = if i = j then α else 0) :
    0 < whiteningSpectralConstant c ∧
      dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
      (dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n)))).toReal ≤
        whiteningSpectralConstant c * n ∧
      dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal (whiteningSpectralConstant c * n) := by
  obtain ⟨hψ0, heven, q, hq, hq0, _hqEven, hqLaw, hqLC⟩ :=
    gaussianGroundstateDensity_strong_logConcave_representative n
      (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ψ hψ r hr hr0 hrEven hrlc hrAE
  let : Measure.IsNegInvariant (densityMeasure n (gaussianGroundstateDensity n
      (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ψ)) := heven
  exact symmetric_body_eigenvalue_bound_of_gaussian_groundstate n hn K hK hconv hinterior hKeven
    ψ hweak hψ hψ0 q hq hq0 hqLaw hqLC c α hc hcα hαOne hcovX

end AffineFKProof
