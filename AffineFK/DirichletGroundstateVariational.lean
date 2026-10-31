module

public import AffineFK.DirichletWeakEigenfunction
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# The genuine Euler equation at a Dirichlet Rayleigh minimizer

Attainment of the actual H0^1 Rayleigh infimum implies the original weak
Dirichlet eigen-equation. This variational lemma does not assert that
attainment exists; the compactness/minimizer construction is separate.
No computed Gaussian-weighted energy is a hypothesis.

The Hilbert norm derivative and Fermat theorem are reused from Mathlib
with their Apache-2.0 contributor attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter
open scoped RealInnerProductSpace ENNReal

set_option maxHeartbeats 1000000 in
theorem dirichletRayleigh_minimizer_energy_lower_bound (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) (hψ : dirichletValue n U ψ ≠ 0)
    (hattain : ENNReal.ofReal (dirichletRayleigh n U ψ) = dirichletEigenvalue n U)
    (w : dirichletSobolev n U) :
    dirichletRayleigh n U ψ * ‖dirichletValue n U w‖ ^ 2 ≤ ‖dirichletGradient n U w‖ ^ 2 := by
  by_cases hw : dirichletValue n U w = 0
  · rw [hw, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    positivity
  · have h := dirichletEigenvalue_le_rayleigh n U w hw
    rw [← hattain] at h
    have hRw : 0 ≤ dirichletRayleigh n U w := by unfold dirichletRayleigh; positivity
    have hreal := (ENNReal.ofReal_le_ofReal_iff hRw).mp h
    change _ ≤ ‖dirichletGradient n U w‖ ^ 2 / ‖dirichletValue n U w‖ ^ 2 at hreal
    exact (le_div_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw))).mp hreal

set_option maxHeartbeats 1000000 in
theorem dirichletRayleigh_attainment_weak_eigenfunction (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) (hψ : dirichletValue n U ψ ≠ 0)
    (hattain : ENNReal.ofReal (dirichletRayleigh n U ψ) = dirichletEigenvalue n U) :
    IsDirichletWeakEigenfunction n U (dirichletRayleigh n U ψ) ψ := by
  intro w
  let ell := dirichletRayleigh n U ψ
  let F : ℝ → ℝ := fun t =>
    ‖dirichletGradient n U (ψ + t • w)‖ ^ 2 - ell * ‖dirichletValue n U (ψ + t • w)‖ ^ 2
  have hzero : F 0 = 0 := by
    simp only [F, zero_smul, add_zero]
    dsimp [ell, dirichletRayleigh]
    field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)]
    ring
  have hmin : IsLocalMin F 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [hzero]
    exact sub_nonneg.mpr (dirichletRayleigh_minimizer_energy_lower_bound n U ψ hψ hattain (ψ + t • w))
  have hG : HasDerivAt (fun t : ℝ => dirichletGradient n U ψ + t • dirichletGradient n U w)
      (dirichletGradient n U w) 0 := by
    simpa only [one_smul] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (dirichletGradient n U w)).const_add (dirichletGradient n U ψ)
  have hV : HasDerivAt (fun t : ℝ => dirichletValue n U ψ + t • dirichletValue n U w)
      (dirichletValue n U w) 0 := by
    simpa only [one_smul] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (dirichletValue n U w)).const_add (dirichletValue n U ψ)
  have hd : HasDerivAt F
      (2 * ⟪dirichletGradient n U ψ, dirichletGradient n U w⟫ -
        ell * (2 * ⟪dirichletValue n U ψ, dirichletValue n U w⟫)) 0 := by
    simpa only [F, map_add, map_smul, zero_smul, add_zero] using!
      hG.norm_sq.sub (hV.norm_sq.const_mul ell)
  have h := hmin.hasDerivAt_eq_zero hd
  change ⟪dirichletGradient n U ψ, dirichletGradient n U w⟫ =
    ell * ⟪dirichletValue n U ψ, dirichletValue n U w⟫
  linarith

end AffineFKProof
