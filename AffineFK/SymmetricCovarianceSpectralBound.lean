module

public import AffineFK.EvenLogConcaveGroundstate
public import AffineFK.GroundstateLogConcaveSpectralClosure

/-!
# The symmetric-body bound from actual restricted-Gaussian covariance

The groundstate, its pointwise log-concave representative and the weighted
law are constructed. The only remaining geometric input is the literal
scalar covariance of the restricted Gaussian with a specified lower bound.
The constant is selected before the dimension, body and covariance scalar.
Universal existence of such a geometric position is a separate theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem symmetric_body_eigenvalue_bound_of_scalar_covariance (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) (heven : ∀ x, -x ∈ K ↔ x ∈ K)
    (c α : ℝ) (hc : 0 < c) (hcα : c ≤ α) (hαOne : α ≤ 1)
    (hcov : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
      ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = if i = j then α else 0) :
    0 < whiteningSpectralConstant c ∧
      dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
      (dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n)))).toReal ≤
        whiteningSpectralConstant c * n ∧
      dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal (whiteningSpectralConstant c * n) := by
  have himage : Neg.neg '' K = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (heven y).mpr hy
    · intro hx
      exact ⟨-x, (heven x).mpr hx, neg_neg x⟩
  have hnegInterior (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) : -x ∈ interior K := by
    have h := (Homeomorph.neg (EuclideanSpace ℝ (Fin n))).isOpenMap.image_interior_subset K
      (show -x ∈ Neg.neg '' interior K from ⟨x, hx, rfl⟩)
    change -x ∈ interior (Neg.neg '' K) at h
    rwa [himage] at h
  let U : Opens (EuclideanSpace ℝ (Fin n)) := ⟨interior K, isOpen_interior⟩
  have hUeven : ∀ x : EuclideanSpace ℝ (Fin n), -x ∈ (U : Set _) ↔ x ∈ (U : Set _) := by
    intro x
    change -x ∈ interior K ↔ x ∈ interior K
    exact ⟨fun hx => by simpa only [neg_neg] using hnegInterior (-x) hx, hnegInterior x⟩
  obtain ⟨ψ, r, hnorm, _hR, _hmin, hweak, hr, hr0, hrEven, hrlc, hrAE⟩ :=
    exists_even_logConcave_dirichlet_groundstate n U hinterior hconv.interior
      (hK.isBounded.subset interior_subset) hUeven
  have hψ : ψ ≠ 0 := by
    intro hzero
    have hz : (0 : ℝ) = 1 := by
      simpa only [hzero, map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using hnorm
    exact zero_ne_one hz
  exact symmetric_body_eigenvalue_bound_of_logConcave_groundstate n hn K hK hconv hinterior heven
    ψ hweak hψ r hr hr0 hrEven hrlc hrAE c α hc hcα hαOne hcov

theorem uniform_symmetric_body_spectral_bound_of_covariance (c : ℝ) (hc : 0 < c) (hcOne : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∀ (K : Set (EuclideanSpace ℝ (Fin n))), IsCompact K → Convex ℝ K →
        (interior K).Nonempty → (∀ x, -x ∈ K ↔ x ∈ K) →
      ∀ (α : ℝ), c ≤ α → α ≤ 1 →
        (∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
          ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) =
            if i = j then α else 0) →
      dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal (C * n) := by
  refine ⟨whiteningSpectralConstant c, whiteningSpectralConstant_pos c hc hcOne, ?_⟩
  intro n hn K hK hconv hinterior heven α hcα hαOne hcov
  exact (symmetric_body_eigenvalue_bound_of_scalar_covariance n hn K hK hconv hinterior heven
    c α hc hcα hαOne hcov).2.2.2

end AffineFKProof
