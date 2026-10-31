module

public import AffineFK.DirichletRayleighFinite

/-!
# The genuine weak Dirichlet eigen-equation on H0^1

This is the usual bilinear weak equation for the actual value and gradient
classes. It assumes no computed weighted-energy or Fisher estimate and
does not assert eigenfunction existence or simplicity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped RealInnerProductSpace

def IsDirichletWeakEigenfunction (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ell : ℝ) (v : dirichletSobolev n U) : Prop :=
  ∀ w : dirichletSobolev n U,
    ⟪dirichletGradient n U v, dirichletGradient n U w⟫ =
      ell * ⟪dirichletValue n U v, dirichletValue n U w⟫

theorem dirichletWeakEigenfunction_integral (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ell : ℝ) (v : dirichletSobolev n U) (hv : IsDirichletWeakEigenfunction n U ell v)
    (w : dirichletSobolev n U) :
    Integrable (fun x => ⟪dirichletGradient n U v x, dirichletGradient n U w x⟫) ∧
    Integrable (fun x => dirichletValue n U v x * dirichletValue n U w x) ∧
    (∫ x, ⟪dirichletGradient n U v x, dirichletGradient n U w x⟫) =
      ell * ∫ x, dirichletValue n U v x * dirichletValue n U w x := by
  have h := hv w
  rw [L2.inner_def, l2_real_inner_integral] at h
  exact ⟨L2.integrable_inner _ _, (Lp.memLp _).integrable_mul (Lp.memLp _), h⟩

theorem dirichletWeakEigenfunction_rayleigh (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ell : ℝ) (v : dirichletSobolev n U) (hv : IsDirichletWeakEigenfunction n U ell v)
    (hne : dirichletValue n U v ≠ 0) : dirichletRayleigh n U v = ell := by
  have h := hv v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (div_eq_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).mpr h

end AffineFKProof
