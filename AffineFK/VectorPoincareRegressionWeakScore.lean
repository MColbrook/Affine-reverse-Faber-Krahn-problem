module

public import AffineFK.VectorPoincareRegression
public import AffineFK.WeakRelativeScoreMoments
public import AffineFK.IsotropicCoordinates

/-!
# Regression for a genuine original weak relative score

The score means and score-coordinate cross moments are conclusions of
the proved compact-cutoff moment identities. Literal isotropic moments
also give the coordinate L2 domain. Smoothness of the actual field and
L2 membership of its actual component gradients remain explicit inputs;
this statement does not assume or prove a full information jump.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ENNReal NNReal ContDiff

theorem weakRelativeScore_poincare_regression (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ≥0) (hP0 : 0 < P) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞))
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hr : MemLp r 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪r x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (hsm : ContDiff ℝ ∞ r)
    (hg : ∀ i : Fin n, MemLp (gradient (fun y => r y i)) 2 ν)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r x + A)) ν ∧
    ((∫ x, ‖r x‖ ^ 2 ∂ν) + matrixHilbertSchmidtSq A) / (P : ℝ) ≤
      ∫ x, matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r x + A) ∂ν := by
  have hxi (i : Fin n) := isotropic_coordinate_memLp n ν hsecond i
  have hm := weakRelativeScore_isotropic_moments n ν hxi hmean hsecond r hr hweak
  exact vectorPoincareRegression n ν P hP0 hP hxi hmean hsecond r hr hm.1 hm.2 hsm hg A

end AffineFKProof
