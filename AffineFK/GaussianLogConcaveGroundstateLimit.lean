module

public import AffineFK.GaussianDirichletMinimizingLimit
public import AffineFK.LogConcaveRepresentativeL2

/-!
# An actual even log-concave H0 groundstate from Gaussian competitors

The input consists of specified nonlocal competitors and their actual
Gaussian energy estimates. Compactness constructs a genuine H0 weak
first eigenfunction; the independently proved L2 representative theorem
then supplies an explicit finite pointwise even log-concave function.
No groundstate log-concavity or pointwise Lp property is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal Topology

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem gaussian_logConcave_groundstate_of_competitors (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (r : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hr : ∀ k, Measurable (r k))
    (hrLp : ∀ k, MemLp (r k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hrnonneg : ∀ k, ∀ᵐ x ∂volume, 0 ≤ r k x)
    (hrlc : ∀ k, LogConcaveDensity (fun x => ENNReal.ofReal (r k x)))
    (hreven : ∀ k x, r k (-x) = r k x)
    (hnorm : ∀ k, ‖(hrLp k).toLp (r k)‖^2 = 1)
    (hsupp : ∀ k, ∀ᵐ x ∂volume,
      x ∉ closure (U : Set (EuclideanSpace ℝ (Fin n))) → r k x = 0)
    (h b : ℕ → ℝ) (hh : ∀ k, 0 < h k) (ht : Tendsto h atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 (dirichletEigenvalue n U).toReal))
    (hform : ∀ k, h1GaussianDirichletForm n (h k) ((hrLp k).toLp (r k)) ≤ b k) :
    ∃ ψ : dirichletSobolev n U, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ‖dirichletValue n U ψ‖^2 = 1 ∧
      dirichletRayleigh n U ψ = (dirichletEigenvalue n U).toReal ∧
      ENNReal.ofReal (dirichletRayleigh n U ψ) = dirichletEigenvalue n U ∧
      IsDirichletWeakEigenfunction n U (dirichletEigenvalue n U).toReal ψ ∧
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∀ x, g (-x) = g x) ∧
      LogConcaveDensity (fun x => ENNReal.ofReal (g x)) ∧
      g =ᵐ[volume] dirichletValue n U ψ := by
  let f : ℕ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    fun k => (hrLp k).toLp (r k)
  have hfSupp (k : ℕ) : ∀ᵐ x ∂volume,
      x ∉ closure (U : Set (EuclideanSpace ℝ (Fin n))) → f k x = 0 := by
    filter_upwards [(hrLp k).coeFn_toLp, hsupp k] with x hx hz hxU
    change (hrLp k).toLp (r k) x = 0
    rw [hx, hz hxU]
  obtain ⟨ψ, s, _hs, hψnorm, hR, hmin, hweak, hlim⟩ :=
    gaussian_supported_normalized_minimizing_limit n U hconv hzero hbounded
      f hnorm hfSupp h b hh ht hb hform
  have hψone : ‖dirichletValue n U ψ‖ = 1 :=
    (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hψnorm)
  obtain ⟨g, hg, hg0, hgeven, hglc, hgae⟩ :=
    exists_even_logConcave_representative_of_L2_tendsto n (fun k => r (s k))
      (fun k => hr (s k)) (fun k => hrLp (s k)) (fun k => hrnonneg (s k))
      (fun k => hrlc (s k)) (fun k => hreven (s k))
      (dirichletValue n U ψ) hψone hlim
  exact ⟨ψ, g, hψnorm, hR, hmin, hweak, hg, hg0, hgeven, hglc, hgae⟩

end AffineFKProof
