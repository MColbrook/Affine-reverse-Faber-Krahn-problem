module

public import AffineFK.WeightedSobolev
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth cutoffs for the weighted Sobolev approximation

The cutoff is a genuine compactly supported smooth test function. Its gradient
bound comes from the supremum norm of its actual compactly supported gradient.
Mathlib's bump functions are due to Sébastien Gouëzel and Yury Kudryashov.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Metric Set
open scoped Distributions

/-- Rescaling a test function by a nonzero homothety preserves its compact
support and smoothness. -/
def scaledTestFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : r ≠ 0) (f : 𝓓((⊤ : Opens E), ℝ)) : 𝓓((⊤ : Opens E), ℝ) :=
  ⟨fun x => f (r⁻¹ • x), f.contDiff.comp (contDiff_const.smul contDiff_id),
    f.hasCompactSupport.comp_homeomorph
      (Homeomorph.smulOfNeZero (r⁻¹) (inv_ne_zero hr)), subset_univ _⟩

theorem scaledTestFunction_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : r ≠ 0) (f : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    scaledTestFunction r hr f x = f (r⁻¹ • x) := by
  rfl

/-- The gradient convention agrees exactly with the Fréchet derivative norm. -/
theorem norm_gradient_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x : E) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

theorem gradient_scaledTestFunction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (r : ℝ) (hr : r ≠ 0) (f : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    gradient (scaledTestFunction r hr f) x = r⁻¹ • gradient f (r⁻¹ • x) := by
  let A : E →L[ℝ] E := r⁻¹ • ContinuousLinearMap.id ℝ E
  have heq : (scaledTestFunction r hr f : E → ℝ) = f ∘ A := by
    funext y
    rfl
  have hdiff : Differentiable ℝ f := f.contDiff.differentiable (by simp)
  have hd := hdiff.differentiableAt.hasFDerivAt.comp x A.hasFDerivAt
  rw [heq, gradient, hd.fderiv]
  have hcomp : (fderiv ℝ f (A x)).comp A = r⁻¹ • fderiv ℝ f (A x) := by
    ext v
    simp only [A, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  rw [hcomp]
  exact (InnerProductSpace.toDual ℝ E).symm.map_smul _ _

theorem gradient_scaledTestFunction_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (r : ℝ) (hr : 0 < r) (f : 𝓓((⊤ : Opens E), ℝ))
    (M : ℝ) (hM : ∀ x, ‖gradient f x‖ ≤ M) (x : E) :
    ‖gradient (scaledTestFunction r hr.ne' f) x‖ ≤ M / r := by
  rw [gradient_scaledTestFunction, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  calc
    _ ≤ r⁻¹ * M := mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.mpr hr.le)
    _ = _ := by ring

/-- A smooth unit cutoff with a genuine uniform gradient bound in every
finite-dimensional Euclidean space, including the zero-dimensional case. -/
theorem exists_smooth_unit_cutoff (n : ℕ) :
    ∃ χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 → χ x = 1) ∧
      (∀ x, 2 ≤ ‖x‖ → χ x = 0) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖gradient χ x‖ ≤ M := by
  let c : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
    ⟨c, c.contDiff, c.hasCompactSupport, subset_univ _⟩
  let G : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    TestFunction.toBoundedContinuousFunctionCLM ℝ (testFunctionGradient χ)
  refine ⟨χ, ?_, ?_, ?_, ‖G‖, norm_nonneg _, ?_⟩
  · intro x
    exact ⟨c.nonneg, c.le_one⟩
  · intro x hx
    apply c.one_of_mem_closedBall
    simpa only [mem_closedBall, dist_zero_right] using hx
  · intro x hx
    apply c.zero_of_le_dist
    simpa only [dist_zero_right] using hx
  · intro x
    have hG : G x = gradient χ x := testFunctionGradient_apply χ x
    rw [← hG]
    exact G.norm_coe_le_norm x

end AffineFKProof
