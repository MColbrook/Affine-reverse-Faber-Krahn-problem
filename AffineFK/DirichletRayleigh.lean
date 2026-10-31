module

public import AffineFK.DirichletSobolev

/-!
# The genuine variational Dirichlet eigenvalue and domain monotonicity

The Rayleigh quotient uses the actual L2 value and gradient of H0^1.
The extended infimum includes all nonzero values, not an unspecified
eigenvalue function. On bounded nonempty domains its eventual real-valued
identification requires a separate finiteness proof; no eigenfunction or
heat-kernel expansion is assumed in this variational definition.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped ENNReal

def dirichletRayleigh (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (v : dirichletSobolev n U) : ℝ :=
  ‖dirichletGradient n U v‖ ^ 2 / ‖dirichletValue n U v‖ ^ 2

def dirichletEigenvalue (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ (v : dirichletSobolev n U) (_ : dirichletValue n U v ≠ 0),
    ENNReal.ofReal (dirichletRayleigh n U v)

theorem dirichletRayleigh_eq_integral (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (v : dirichletSobolev n U) :
    dirichletRayleigh n U v =
      (∫ x, ‖dirichletGradient n U v x‖ ^ 2) / (∫ x, (dirichletValue n U v x) ^ 2) := by
  simp only [dirichletRayleigh, l2_norm_sq_integral, Real.norm_eq_abs, sq_abs]

theorem dirichletEigenvalue_le_rayleigh (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (v : dirichletSobolev n U) (hv : dirichletValue n U v ≠ 0) :
    dirichletEigenvalue n U ≤ ENNReal.ofReal (dirichletRayleigh n U v) :=
  iInf_le_of_le v (iInf_le _ hv)

set_option maxHeartbeats 800000 in
theorem dirichletEigenvalue_antitone (n : ℕ) (U V : Opens (EuclideanSpace ℝ (Fin n)))
    (hUV : U ≤ V) : dirichletEigenvalue n V ≤ dirichletEigenvalue n U := by
  apply le_iInf
  intro v
  apply le_iInf
  intro hv
  have h := dirichletEigenvalue_le_rayleigh n V (dirichletInclusion n U V hUV v)
    (by simpa only [dirichletInclusion_value] using hv)
  simpa only [dirichletRayleigh, dirichletInclusion_value, dirichletInclusion_gradient] using h

end AffineFKProof
