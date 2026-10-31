module

public import AffineFK.GaussianLogConcaveGroundstateLimit
public import AffineFK.GaussianKilledApproximation
public import AffineFK.DirichletEigenvaluePositive

/-!
# An even log-concave actual first Dirichlet groundstate

Finite Gaussian killing powers provide the actual normalized competitors.
Their nonlocal forms approach the energy of an attained H0 minimizer.
The vanishing-time compactness and pointwise representative limits then
construct an even log-concave first weak eigenfunction. No smooth boundary,
strict positivity, simplicity or groundstate log-concavity is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter Set
open scoped ENNReal Topology

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem exists_even_logConcave_dirichlet_groundstate (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hne : (U : Set (EuclideanSpace ℝ (Fin n))).Nonempty)
    (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (heven : ∀ x : EuclideanSpace ℝ (Fin n), -x ∈ (U : Set _) ↔ x ∈ (U : Set _)) :
    ∃ ψ : dirichletSobolev n U, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ‖dirichletValue n U ψ‖^2 = 1 ∧
      dirichletRayleigh n U ψ = (dirichletEigenvalue n U).toReal ∧
      ENNReal.ofReal (dirichletRayleigh n U ψ) = dirichletEigenvalue n U ∧
      IsDirichletWeakEigenfunction n U (dirichletEigenvalue n U).toReal ψ ∧
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∀ x, g (-x) = g x) ∧
      LogConcaveDensity (fun x => ENNReal.ofReal (g x)) ∧
      g =ᵐ[volume] dirichletValue n U ψ := by
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set _) := by
    obtain ⟨x, hx⟩ := hne
    have hm := hconv hx ((heven x).mpr hx)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simpa only [smul_neg, add_neg_cancel] using hm
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) (U : Set _) ≠ ∞ :=
    ne_top_of_le_ne_top hbounded.isCompact_closure.measure_lt_top.ne (measure_mono subset_closure)
  obtain ⟨v, hvnorm, hvR, _hvmin, _hvweak⟩ :=
    dirichletEigenvalue_attained_of_bounded n U hne hbounded
  have hvone : ‖dirichletValue n U v‖ = 1 :=
    (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hvnorm)
  have hvenergy : ‖dirichletGradient n U v‖^2 = (dirichletEigenvalue n U).toReal := by
    simpa only [dirichletRayleigh, hvnorm, div_one] using hvR
  have hvsupp := dirichletValue_ae_zero_outside n U (U : Set _) U.isOpen.measurableSet
    (Subset.refl _) v
  let h : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hh (j : ℕ) : 0 < h j := by dsimp [h]; positivity
  have ht : Tendsto h atTop (𝓝 (0 : ℝ)) := tendsto_inverse_succ
  let b : ℕ → ℝ := fun j => (dirichletEigenvalue n U).toReal + h j
  have hb : Tendsto b atTop (𝓝 (dirichletEigenvalue n U).toReal) := by
    simpa only [b, add_zero] using tendsto_const_nhds.add ht
  choose k hk using fun j => gaussianKillingNormalized_exists_H1_energy_le n
    (U : Set _) U.isOpen hne hfin (h j) (hh j) (h j) (hh j)
    (v : unweightedSobolevGraph n) hvone hvsupp
  let r : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun j =>
    gaussianKillingNormalizedFunction n (U : Set _) U.isOpen.measurableSet hfin (h j) (hh j) (k j)
  have hrLp (j : ℕ) : MemLp (r j) 2 volume :=
    gaussianKillingNormalizedFunction_memLp n _ U.isOpen.measurableSet hfin (h j) (hh j) (k j)
  have hrL2 (j : ℕ) : (hrLp j).toLp (r j) =
      gaussianKillingNormalizedL2 n (U : Set _) U.isOpen.measurableSet hfin (h j) (hh j) (k j) := by
    apply Lp.ext
    exact (hrLp j).coeFn_toLp.trans
      (gaussianKillingNormalizedL2_coe n _ U.isOpen.measurableSet hfin (h j) (hh j) (k j)).symm
  have hnorm (j : ℕ) : ‖(hrLp j).toLp (r j)‖^2 = 1 := by
    rw [hrL2, gaussianKillingNormalizedL2_norm n _ U.isOpen hne hfin (h j) (hh j) (k j), one_pow]
  have hsupp (j : ℕ) : ∀ᵐ x ∂volume, x ∉ closure (U : Set _) → r j x = 0 :=
    Eventually.of_forall fun x hx => gaussianKillingNormalizedFunction_zero_exterior n _
      U.isOpen.measurableSet hfin (h j) (hh j) (k j) x (fun hxU => hx (subset_closure hxU))
  have hform (j : ℕ) : h1GaussianDirichletForm n (h j) ((hrLp j).toLp (r j)) ≤ b j := by
    rw [hrL2]
    have hbound := hk j
    change h1GaussianDirichletForm n (h j)
      (gaussianKillingNormalizedL2 n (U : Set _) U.isOpen.measurableSet hfin (h j) (hh j) (k j)) ≤
        ‖dirichletGradient n U v‖^2 + h j at hbound
    simpa only [b, hvenergy] using hbound
  exact gaussian_logConcave_groundstate_of_competitors n U hconv hzero hbounded r
    (fun j => gaussianKillingNormalizedFunction_measurable n _ U.isOpen.measurableSet hfin (h j) (hh j) (k j))
    hrLp
    (fun j => Eventually.of_forall (gaussianKillingNormalizedFunction_nonneg n _ U.isOpen.measurableSet hfin (h j) (hh j) (k j)))
    (fun j => gaussianKillingNormalizedFunction_logConcave n _ U.isOpen.measurableSet hfin hconv (h j) (hh j) (k j))
    (fun j => gaussianKillingNormalizedFunction_even n _ U.isOpen.measurableSet hfin
      (fun x hx => (heven x).mpr hx) (h j) (hh j) (k j))
    hnorm hsupp h b hh ht hb hform

end AffineFKProof
