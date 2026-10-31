module

public import AffineFK.GaussianKernelDerivativeBounds

/-!
# The genuine Gaussian multipliers for the Dirichlet ground state

The two functions are globally smooth and positive. Their values and
actual gradients are bounded on all of Euclidean space, so their action
on the genuine zero-boundary Sobolev domain requires no boundary
regularity of the open set. These are scalar multiplier facts only;
no eigenfunction or computed ground-state energy is assumed here.

The derivative and exponential estimates use Mathlib's real Hilbert-space
calculus and exponential inequalities (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open scoped ContDiff RealInnerProductSpace

def groundstateGaussianFactor (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-(‖x‖ ^ 2 / 4))

def groundstateGaussianWeight (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-(‖x‖ ^ 2 / 2))

theorem groundstateGaussianFactor_pos (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0 < groundstateGaussianFactor n x := Real.exp_pos _

theorem groundstateGaussianFactor_smooth (n : ℕ) :
    ContDiff ℝ ∞ (groundstateGaussianFactor n) := by
  have hq : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => -(1 / 4 : ℝ) * ‖x‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  convert Real.contDiff_exp.comp hq using 1
  funext x
  dsimp [groundstateGaussianFactor]
  congr 1
  ring

theorem groundstateGaussianFactor_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (groundstateGaussianFactor n x) ^ 2 = groundstateGaussianWeight n x := by
  simp only [groundstateGaussianFactor, groundstateGaussianWeight, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem groundstateGaussianFactor_gradient (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (groundstateGaussianFactor n) x =
      (-(groundstateGaussianFactor n x) / 2) • x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(1 / 4 : ℝ))).exp
  have he : (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-(1 / 4 : ℝ) * ‖y‖ ^ 2)) =
      groundstateGaussianFactor n := by
    funext y
    dsimp [groundstateGaussianFactor]
    congr 1
    ring
  rw [he] at h
  have hscalar : Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2) = groundstateGaussianFactor n x :=
    congrFun he x
  rw [hscalar] at h
  have hlinear : groundstateGaussianFactor n x • (-(1 / 4 : ℝ)) • 2 • (innerSL ℝ) x =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
        ((-(groundstateGaussianFactor n x) / 2) • x) := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply] <;> ring
  rw [hlinear] at h
  have hd : HasFDerivAt (groundstateGaussianFactor n)
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
        ((-(groundstateGaussianFactor n x) / 2) • x)) x := by
    simpa only using! h
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

theorem groundstateGaussianFactor_le_one (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    groundstateGaussianFactor n x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (by positivity)

theorem groundstateGaussianFactor_norm_mul_le (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ * groundstateGaussianFactor n x ≤ 5 := by
  let r := ‖x‖
  let m := groundstateGaussianFactor n x
  have hr : 0 ≤ r := norm_nonneg x
  have hm : 0 ≤ m := (groundstateGaussianFactor_pos n x).le
  have hm1 : m ≤ 1 := groundstateGaussianFactor_le_one n x
  have he : r ^ 2 / 4 ≤ Real.exp (r ^ 2 / 4) := by
    have h := Real.add_one_le_exp (r ^ 2 / 4)
    linarith
  have hprod : Real.exp (r ^ 2 / 4) * m = 1 := by
    dsimp [m, r, groundstateGaussianFactor]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hb := mul_le_mul_of_nonneg_right he hm
  rw [hprod] at hb
  have hr2 : r ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg (r - 1 / 2)]
  have hmul := mul_le_mul_of_nonneg_right hr2 hm
  nlinarith

theorem groundstateGaussianFactor_gradient_bound (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (groundstateGaussianFactor n) x‖ ≤ 5 / 2 := by
  rw [groundstateGaussianFactor_gradient, norm_smul, Real.norm_eq_abs,
    abs_div, abs_neg, abs_of_pos (groundstateGaussianFactor_pos n x), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [groundstateGaussianFactor_norm_mul_le n x]

theorem groundstateGaussianWeight_smooth (n : ℕ) :
    ContDiff ℝ ∞ (groundstateGaussianWeight n) := by
  have hq : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => -(1 / 2 : ℝ) * ‖x‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  convert Real.contDiff_exp.comp hq using 1
  funext x
  dsimp [groundstateGaussianWeight]
  congr 1
  ring

theorem groundstateGaussianWeight_gradient (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (groundstateGaussianWeight n) x = -(groundstateGaussianWeight n x) • x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(1 / 2 : ℝ))).exp
  have he : (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-(1 / 2 : ℝ) * ‖y‖ ^ 2)) =
      groundstateGaussianWeight n := by
    funext y
    dsimp [groundstateGaussianWeight]
    congr 1
    ring
  rw [he] at h
  have hscalar : Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) = groundstateGaussianWeight n x :=
    congrFun he x
  rw [hscalar] at h
  have hlinear : groundstateGaussianWeight n x • (-(1 / 2 : ℝ)) • 2 • (innerSL ℝ) x =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
        (-(groundstateGaussianWeight n x) • x) := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply] <;> ring
  rw [hlinear] at h
  have hd : HasFDerivAt (groundstateGaussianWeight n)
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
        (-(groundstateGaussianWeight n x) • x)) x := by
    simpa only using! h
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

theorem groundstateGaussianWeight_bound (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0 < groundstateGaussianWeight n x ∧ groundstateGaussianWeight n x ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))⟩

theorem groundstateGaussianWeight_gradient_bound (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (groundstateGaussianWeight n) x‖ ≤ 5 := by
  have h := groundstateGaussianFactor_norm_mul_le n x
  have hm := groundstateGaussianFactor_le_one n x
  have hp := (groundstateGaussianFactor_pos n x).le
  rw [groundstateGaussianWeight_gradient, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (groundstateGaussianWeight_bound n x).1, ← groundstateGaussianFactor_sq]
  have hh : (groundstateGaussianFactor n x) ^ 2 ≤ groundstateGaussianFactor n x := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hh (norm_nonneg x)]

end AffineFKProof
