module

public import AffineFK.GaussianRelativeScore
public import AffineFK.FiniteSobolevRelativeScore
public import AffineFK.UnweightedSobolevSmoothApproximation
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Sobolev information of a positive smooth density

The square root has its actual Frechet gradient. The logarithmic relative
score therefore has exactly the manuscript's square-root-density energy.
All global L2 and graph membership assertions below require their genuine
integrability hypotheses; pointwise calculus alone is not used for them.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

theorem smooth_density_gradient_sqrt (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => Real.sqrt (ρ y)) x =
      (Real.sqrt (ρ x) / 2) • gradient (fun y => Real.log (ρ y)) x := by
  have hd := ((hρ.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt
  have hs := hd.sqrt (hρpos x).ne'
  have hl := hd.log (hρpos x).ne'
  change (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (fun y => Real.sqrt (ρ y)) x) =
    (Real.sqrt (ρ x) / 2) • (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ (fun y => Real.log (ρ y)) x)
  rw [hs.fderiv, hl.fderiv, map_smul, map_smul, smul_smul]
  congr 1
  have hspos : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.mpr (hρpos x)
  field_simp [(hρpos x).ne', hspos.ne']
  nlinarith [Real.sq_sqrt (hρpos x).le]

theorem smooth_density_sqrt_gradient_norm (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (fun y => Real.sqrt (ρ y)) x‖ ^ 2 =
      (1 / 4 : ℝ) * ρ x * ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 := by
  rw [smooth_density_gradient_sqrt n ρ hρ hρpos x, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (hρpos x).le]
  ring

theorem smooth_density_relative_energy_pointwise (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    ‖(2 : ℝ) • gradient (fun y => Real.sqrt (ρ y)) x + Real.sqrt (ρ x) • x‖ ^ 2 =
      ρ x * ‖gaussianRelativeScore n ρ x‖ ^ 2 := by
  have heq : (2 : ℝ) • gradient (fun y => Real.sqrt (ρ y)) x + Real.sqrt (ρ x) • x =
      Real.sqrt (ρ x) • gaussianRelativeScore n ρ x := by
    rw [smooth_density_gradient_sqrt n ρ hρ hρpos x]
    ext i
    simp only [gaussianRelativeScore, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    ring
  rw [heq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hρpos x).le]

end AffineFKProof
