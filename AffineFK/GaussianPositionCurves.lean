module

public import AffineFK.GaussianPositionAction
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Explicit determinant-one variations

Shears and trace-free diagonal exponentials are literal special-linear
matrices for every parameter. Their derivatives follow from the scalar
derivative and finite-dimensional linear transport, without assuming a
matrix-exponential determinant formula.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Elementwise

def gaussianPositionShear (n : ℕ) (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    Matrix.SpecialLinearGroup (Fin n) ℝ :=
  ⟨Matrix.transvection i j t, Matrix.det_transvection_of_ne i j hij t⟩

def gaussianPositionDiagonal (n : ℕ) (d : Fin n → ℝ) (hd : ∑ i, d i = 0) (t : ℝ) :
    Matrix.SpecialLinearGroup (Fin n) ℝ :=
  ⟨Matrix.diagonal (fun i => Real.exp (t * d i)), by
    rw [Matrix.det_diagonal, ← Real.exp_sum, ← Finset.mul_sum, hd, mul_zero, Real.exp_zero]⟩

def gaussianPositionMatrixTransport (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap

theorem gaussianPositionShear_hasDerivAt (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    HasDerivAt
      (fun t : ℝ => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (gaussianPositionShear n i j hij t : Matrix (Fin n) (Fin n) ℝ))
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.single i j 1)) 0 := by
  have hmat : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) +
      t • Matrix.single i j 1) (Matrix.single i j 1) 0 := by
    simpa only [one_smul, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).smul_const (Matrix.single i j (1 : ℝ))).const_add 1)
  have heq (t : ℝ) : (1 : Matrix (Fin n) (Fin n) ℝ) + t • Matrix.single i j 1 =
      (gaussianPositionShear n i j hij t : Matrix (Fin n) (Fin n) ℝ) := by
    ext k l
    simp [gaussianPositionShear, Matrix.transvection, Matrix.single_apply]
  have hmat' : HasDerivAt
      (fun t => (gaussianPositionShear n i j hij t : Matrix (Fin n) (Fin n) ℝ))
      (Matrix.single i j 1) 0 := by
    simpa only [heq] using hmat
  exact (gaussianPositionMatrixTransport n).hasFDerivAt.comp_hasDerivAt 0 hmat'

theorem gaussianPositionDiagonal_hasDerivAt (n : ℕ)
    (d : Fin n → ℝ) (hd : ∑ i, d i = 0) :
    HasDerivAt
      (fun t : ℝ => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (gaussianPositionDiagonal n d hd t : Matrix (Fin n) (Fin n) ℝ))
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal d)) 0 := by
  have hmat : HasDerivAt
      (fun t : ℝ => Matrix.diagonal (fun i => Real.exp (t * d i))) (Matrix.diagonal d) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq, Function.comp_def, id_eq, zero_mul,
        Real.exp_zero, one_mul] using
        (Real.hasDerivAt_exp (0 * d i)).comp 0 ((hasDerivAt_id (0 : ℝ)).mul_const (d i))
    · simpa only [Matrix.diagonal_apply, hij, ↓reduceIte] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  exact (gaussianPositionMatrixTransport n).hasFDerivAt.comp_hasDerivAt 0 hmat

theorem gaussianPositionShear_zero (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (gaussianPositionShear n i j hij 0 : Matrix (Fin n) (Fin n) ℝ) =
      ContinuousLinearMap.id ℝ _ := by
  simpa [gaussianPositionShear] using (show (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n)) = ContinuousLinearMap.id ℝ _ from rfl)

theorem gaussianPositionDiagonal_zero (n : ℕ) (d : Fin n → ℝ) (hd : ∑ i, d i = 0) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (gaussianPositionDiagonal n d hd 0 : Matrix (Fin n) (Fin n) ℝ) =
      ContinuousLinearMap.id ℝ _ := by
  simpa [gaussianPositionDiagonal, Matrix.diagonal_one] using (show
    (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      ContinuousLinearMap.id ℝ _ from rfl)

end AffineFKProof
