module

public import AffineFK.ConvexPotentialHessian
public import AffineFK.EuclideanPartialCalculus
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual unit strong convexity and the component Hessian

Convexity of W minus the half squared norm implies that the actual
Hessian of W minus the identity is positive semidefinite. The derivative
of the quadratic and the subtraction identities are proved explicitly;
neither a Hessian sign nor a Brascamp--Lieb conclusion is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open TopologicalSpace InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace

theorem strongLogConcave_halfNormSq_gradient (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y : EuclideanSpace ℝ (Fin n) => (1 / 2 : ℝ) * ‖y‖ ^ 2) x = x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ)
  have hlin : (1 / 2 : ℝ) • 2 • (innerSL ℝ) x =
      (toDual ℝ (EuclideanSpace ℝ (Fin n))) x := by
    ext y
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
      toDual_apply_apply, innerSL_apply_apply]
    ring
  rw [hlin] at h
  have hd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => (1 / 2 : ℝ) * ‖y‖ ^ 2)
      ((toDual ℝ (EuclideanSpace ℝ (Fin n))) x) x := by
    simpa only using! h
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

theorem strongLogConcave_gradient_sub (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => f y - g y) x = gradient f x - gradient g x := by
  simp only [gradient, fderiv_fun_sub (hf x) (hg x), map_sub]

theorem strongLogConcave_hessian_sub_halfNormSq (n : ℕ)
    (W : EuclideanSpace ℝ (Fin n) → ℝ) (hW : ContDiff ℝ ∞ W)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.of (fun i j : Fin n => gradient (fun y =>
      gradient (fun z => W z - (1 / 2 : ℝ) * ‖z‖ ^ 2) y i) x j) =
      Matrix.of (fun i j : Fin n => gradient (fun y => gradient W y i) x j) -
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hq : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => (1 / 2 : ℝ) * ‖z‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have heq : gradient (fun z => W z - (1 / 2 : ℝ) * ‖z‖ ^ 2) =
      fun y => gradient W y - y := by
    funext y
    rw [strongLogConcave_gradient_sub n W _
      (hW.differentiable (by simp)) (hq.differentiable (by simp)),
      strongLogConcave_halfNormSq_gradient]
  ext i j
  rw [heq]
  have hci : ContDiff ℝ ∞ (fun y => gradient W y i) := by
    have h := (coordinateFunctional n i).contDiff.comp
      (contDiff_gradient_of_contDiff n W hW)
    simpa only [Function.comp_def, coordinateFunctional_apply] using! h
  have hci' : Differentiable ℝ (fun y : EuclideanSpace ℝ (Fin n) => y i) := by
    have he : (fun y : EuclideanSpace ℝ (Fin n) => y i) = coordinateFunctional n i :=
      funext fun y => (coordinateFunctional_apply n i y).symm
    rw [he]
    exact (coordinateFunctional n i).differentiable
  simp only [PiLp.sub_apply]
  change gradient (fun y => gradient W y i - y i) x j =
    gradient (fun y => gradient W y i) x j - (1 : Matrix (Fin n) (Fin n) ℝ) i j
  rw [strongLogConcave_gradient_sub n _ _ (hci.differentiable (by simp)) hci']
  change gradient (fun y => gradient W y i) x j - gradient (fun y => y i) x j = _
  rw [gradient_coordinate_eq_fderiv n (fun y => y i) x j]
  have hc : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => y i) x
      (EuclideanSpace.basisFun (Fin n) ℝ j) = if i = j then 1 else 0 :=
    euclideanPartial_coordinate n i j x
  rw [hc]
  simp only [Matrix.one_apply]

theorem strongLogConcave_convex_potential_hessian (n : ℕ)
    (W : EuclideanSpace ℝ (Fin n) → ℝ) (hW : ContDiff ℝ ∞ W)
    (hconv : ConvexOn ℝ Set.univ (fun x => W x - (1 / 2 : ℝ) * ‖x‖ ^ 2))
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.PosSemidef (Matrix.of (fun i j : Fin n => gradient (fun y => gradient W y i) x j) -
      (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  have hq : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => (1 / 2 : ℝ) * ‖z‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have h := convex_potential_hessian_posSemidef n _ (hW.sub hq) hconv x
  change Matrix.PosSemidef (Matrix.of (fun i j : Fin n => gradient (fun y =>
    gradient (fun z => W z - (1 / 2 : ℝ) * ‖z‖ ^ 2) y i) x j)) at h
  rwa [strongLogConcave_hessian_sub_halfNormSq n W hW x] at h

end AffineFKProof
