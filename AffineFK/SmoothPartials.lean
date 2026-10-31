module

public import AffineFK.SteinTestIdentities
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Hessian ordering for smooth compactly supported tests

The iterated partials used in the Poisson argument agree with the two
evaluations of the genuine second Frechet derivative. Schwarz symmetry
therefore identifies their order with the manuscript's Hessian convention.
The symmetry theorem is reused from Mathlib's FDeriv.Symmetric development.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff

theorem partialTest_second_fderiv
    (n : ℕ) (j k : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n j (partialTest n k φ) x =
      fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) := by
  have hc : ContDiff ℝ (1 + 1 : ℕ∞ω) (φ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    φ.contDiff.of_le (by simp)
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (contDiff_succ_iff_fderiv.mp hc).2.2.differentiable (by norm_num)
  have heq : (partialTest n k φ : EuclideanSpace ℝ (Fin n) → ℝ) =
      (fun y => fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ k)) :=
    funext (partialTest_fderiv n k φ)
  rw [partialTest_fderiv, heq, fderiv_clm_apply (hd x)
    (differentiableAt_const (EuclideanSpace.basisFun (Fin n) ℝ k))]
  simp

theorem partialTest_commute
    (n : ℕ) (j k : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n j (partialTest n k φ) x = partialTest n k (partialTest n j φ) x := by
  rw [partialTest_second_fderiv, partialTest_second_fderiv]
  exact (φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

end AffineFKProof
