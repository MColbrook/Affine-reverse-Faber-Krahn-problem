module

public import AffineFK.GaussianSmoothedScoreHessianSymmetry
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Coordinate calculus for the actual Euclidean derivatives

The coordinate operator is the actual Frechet derivative evaluated on a
standard orthonormal basis vector. Product, sum and commutation rules
reuse Mathlib's Frechet calculus and Schwarz theorem (Sebastien Gouezel,
Yury Kudryashov and contributors, Apache-2.0). All dimensions, including
zero, are retained.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace

def euclideanPartial (n : ℕ) (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)

theorem euclideanPartial_eq_gradient (n : ℕ) (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i f x = gradient f x i :=
  (gradient_coordinate_eq_fderiv n f x i).symm

theorem euclideanPartial_smooth (n : ℕ) (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (euclideanPartial n i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem euclideanPartial_const (n : ℕ) (i : Fin n) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (fun _ => c) x = 0 := by
  simp [euclideanPartial]

theorem euclideanPartial_add (n : ℕ) (i : Fin n)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (fun y => f y + g y) x =
      euclideanPartial n i f x + euclideanPartial n i g x := by
  unfold euclideanPartial
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

theorem euclideanPartial_mul (n : ℕ) (i : Fin n)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (fun y => f y * g y) x =
      f x * euclideanPartial n i g x + g x * euclideanPartial n i f x := by
  unfold euclideanPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

theorem euclideanPartial_sum (n : ℕ) (i : Fin n) {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (fun y => ∑ j, f j y) x = ∑ j, euclideanPartial n i (f j) x := by
  classical
  unfold euclideanPartial
  rw [fderiv_fun_sum (fun j _ => (hf j).differentiable (by simp) x)]
  simp only [sum_apply]

theorem euclideanPartial_commute (n : ℕ) (i j : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n j (euclideanPartial n i f) x =
      euclideanPartial n i (euclideanPartial n j f) x := by
  simp_rw [funext (euclideanPartial_eq_gradient n i f),
    funext (euclideanPartial_eq_gradient n j f), euclideanPartial_eq_gradient]
  exact smooth_hessian_component_symmetric n f hf x i j

theorem euclideanPartial_coordinate (n : ℕ) (i j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n j (fun y => y i) x = if i = j then 1 else 0 := by
  have h : (fun y : EuclideanSpace ℝ (Fin n) => y i) = coordinateFunctional n i :=
    funext fun y => (coordinateFunctional_apply n i y).symm
  rw [h]
  unfold euclideanPartial
  rw [(coordinateFunctional n i).fderiv]
  simp [coordinateFunctional_apply, EuclideanSpace.basisFun_apply, eq_comm]

end AffineFKProof
