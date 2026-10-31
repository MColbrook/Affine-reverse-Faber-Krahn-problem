module

public import AffineFK.GaussianSmoothedScoreDifferential
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Genuine Hessian ordering and symmetry for the smoothed logarithmic density

The component-gradient convention is exactly (i,j) = partial_j partial_i.
It is identified with the true second Frechet derivative evaluated on the
ordered basis vectors e_j,e_i before Schwarz symmetry is applied. This
does not assert a density-ratio formula or Hessian integrability.

Schwarz symmetry reuses Mathlib's FDeriv.Symmetric development by
Sebastien Gouezel and contributors (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped ContDiff RealInnerProductSpace

theorem gradient_coordinate_eq_fderiv (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    gradient f x i = fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [← inner_gradient_left, real_inner_comm]
  exact (EuclideanSpace.basisFun_inner (Fin n) ℝ (gradient f x) i).symm

theorem gradient_component_second_fderiv (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    gradient (fun y => gradient f y i) x j =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd : Differentiable ℝ (fderiv ℝ f) := hfd.differentiable (by simp)
  have heq : (fun y => gradient f y i) =
      fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin n) ℝ i) :=
    funext fun y => gradient_coordinate_eq_fderiv n f y i
  rw [gradient_coordinate_eq_fderiv, heq, fderiv_clm_apply (hd x)
    (differentiableAt_const (EuclideanSpace.basisFun (Fin n) ℝ i))]
  simp

theorem smooth_hessian_component_symmetric (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    gradient (fun y => gradient f y i) x j = gradient (fun y => gradient f y j) x i := by
  rw [gradient_component_second_fderiv n f hf, gradient_component_second_fderiv n f hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

theorem logDensity_hessian_component_symmetric (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    gradient (fun y => gradient (fun z => Real.log (ρ z)) y i) x j =
      gradient (fun y => gradient (fun z => Real.log (ρ z)) y j) x i :=
  smooth_hessian_component_symmetric n _ (hρ.log (fun y => (hρpos y).ne')) x i j

theorem gaussianSmoothing_ordinaryScore_hessian_component_symmetric (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    gradient (fun y => gradient (fun z => Real.log (gaussianSmoothingDensity n ν a b z)) y i) x j =
      gradient (fun y => gradient (fun z => Real.log (gaussianSmoothingDensity n ν a b z)) y j) x i :=
  logDensity_hessian_component_symmetric n _ (gaussianSmoothingDensity_smooth n ν a b)
    (gaussianSmoothingDensity_pos n ν a b hb) x i j

end AffineFKProof
