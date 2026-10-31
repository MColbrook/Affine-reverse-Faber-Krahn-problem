module

public import AffineFK.ConvexPotentialHessianLine
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive semidefiniteness of the actual component Hessian

Finite orthonormal-basis expansion identifies the matrix quadratic form
with the actual second Frechet derivative. The genuine convex-line
inequality and Schwarz symmetry then give positive semidefiniteness.
No matrix sign or second-derivative sign is a hypothesis.

Matrix PSD reuses Mathlib's development by Alexander Bentkamp and
Mohanad Ahmed; orthonormal expansion and Schwarz symmetry retain their
primary Mathlib attribution (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open TopologicalSpace InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace

theorem potential_hessian_quadratic_form (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x v : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ∑ j, v i * gradient (fun y => gradient f y i) x j * v j) =
      fderiv ℝ (fderiv ℝ f) x v v := by
  let B := fderiv ℝ (fderiv ℝ f) x
  have hv : (∑ i : Fin n, v i • EuclideanSpace.basisFun (Fin n) ℝ i) = v := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  have hB : B v v = ∑ i : Fin n, ∑ j : Fin n,
      v i * v j * B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    calc
      _ = B (∑ i : Fin n, v i • EuclideanSpace.basisFun (Fin n) ℝ i)
          (∑ j : Fin n, v j • EuclideanSpace.basisFun (Fin n) ℝ j) := by rw [hv]
      _ = _ := by
        simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hsym : B (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) =
            B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) :=
          (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _
        rw [hsym]
        ring
  have hentry (i j : Fin n) :
      gradient (fun y => gradient f y i) x j =
        B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    rw [gradient_component_second_fderiv n f hf]
    exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
        v i * v j * B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hentry]
      ring
    _ = _ := hB.symm

theorem convex_potential_hessian_posSemidef (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hconv : ConvexOn ℝ Set.univ f) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.PosSemidef (fun i j : Fin n => gradient (fun y => gradient f y i) x j) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using smooth_hessian_component_symmetric n f hf x j i
  · intro v
    let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have h := convex_potential_second_fderiv_nonneg n f hf hconv x w
    rw [← potential_hessian_quadratic_form n f hf x w] at h
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    simpa only [w, PiLp.toLp_apply, mul_assoc] using h

theorem potential_hessian_neg (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    (fun i j : Fin n => gradient (fun y => gradient (fun z => -f z) y i) x j) =
      -(fun i j : Fin n => gradient (fun y => gradient f y i) x j) := by
  ext i j
  change gradient (fun y => gradient (fun z => -f z) y i) x j =
    -gradient (fun y => gradient f y i) x j
  rw [gradient_component_second_fderiv n _ hf.neg, gradient_component_second_fderiv n f hf]
  have heq : fderiv ℝ (fun z => -f z) = fun z => -fderiv ℝ f z :=
    funext fun z => fderiv_fun_neg
  rw [heq, fderiv_fun_neg]
  simp only [ContinuousLinearMap.neg_apply]

theorem concave_potential_negative_hessian_posSemidef (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hconc : ConcaveOn ℝ Set.univ f) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.PosSemidef (-(fun i j : Fin n => gradient (fun y => gradient f y i) x j)) := by
  have h := convex_potential_hessian_posSemidef n (fun z => -f z) hf.neg hconc.neg x
  rwa [potential_hessian_neg n f hf x] at h

end AffineFKProof
