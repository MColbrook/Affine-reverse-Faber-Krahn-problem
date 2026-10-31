module

public import AffineFK.ConvexPotentialHessian
public import AffineFK.LogConcaveDensityLog
public import AffineFK.GaussianHessianL2Calculus

/-!
# The negative actual log-density Hessian of a positive smooth log-concave density

The genuine extended log-concavity premise gives concavity of the actual
real logarithm. The generic convex-potential result proves the matrix
sign; positive semidefiniteness is not a premise. The named matrix is the
same actual component Hessian as in the separate L2 calculus module.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

theorem logConcaveDensity_negative_logHessian_posSemidef (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (ρ x)))
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.PosSemidef (-(fun i j : Fin n => gradient (fun y => gradient (fun z => Real.log (ρ z)) y i) x j)) :=
  concave_potential_negative_hessian_posSemidef n _
    (hρ.log (fun y => (hρpos y).ne')) (logConcaveDensity_concaveOn_log ρ hρpos hlc) x

theorem logConcaveDensity_densityLogHessian_neg_posSemidef (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (ρ x)))
    (x : EuclideanSpace ℝ (Fin n)) :
    (-densityLogHessian n ρ x).PosSemidef :=
  logConcaveDensity_negative_logHessian_posSemidef n ρ hρ hρpos hlc x

end AffineFKProof
