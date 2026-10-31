module

public import AffineFK.BridgeDirichletRayleigh
public import AffineFK.BridgeKilledSurvivalBounds
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Actual variational Rayleigh bound from the Gaussian dilation profile

The genuine independent Gaussian coefficient event supplies the survival
bound. Its actual continuous bridge law gives the particular killed
diagonal; proved row H1 energy and the actual H0 converse give the literal
variational eigenvalue. No Anderson/correlation, spectral expansion, or
heat-kernel identification hypothesis is introduced.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal Pointwise

theorem bridge_dirichletEigenvalue_le_unit_survival (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (B : ℝ) (hunit : ENNReal.ofReal (Real.exp (-B)) ≤
      bridgeSeriesLaw n (bridgeBrownianSurvivalSet n U)) :
    dirichletEigenvalue n U ≤ ENNReal.ofReal (8*B + 4*(n : ℝ)*Real.log 2) := by
  have hpos (r : ℝ) (hr : (1/4 : ℝ) ≤ r) (hrupper : r ≤ 3*(1/4 : ℝ)) :
      0 < bridgeKilledDiagonal n r 0 U :=
    (bridgeKilledDiagonal_pos_and_log_lower n U hconv hzero B hunit r
      (by linarith) (by linarith)).1
  have h := bridge_dirichletEigenvalue_le_log_diagonal n U hconv hzero hbounded
    (1/4) (by norm_num) hpos
  have hl := bridgeKilledDiagonal_log_double_bound n U hconv hzero B hunit
    (1/4) (by norm_num) (by norm_num)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  norm_num only [div_div, div_one, one_div, inv_div, inv_one] at *
  nlinarith

def bridgeProfileOpenDomain (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (α : ℝ) (hα : α < 1/2) : Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨(2*bridgeRadius α) • interior D,
    isOpen_interior.smul₀ (ne_of_gt (mul_pos (by norm_num) (bridgeRadius_pos α hα)))⟩

theorem bridge_dirichletEigenvalue_le_dilation_profile (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D)
    (hconvex : Convex ℝ D) (hzero : 0 ∈ interior D)
    (p α A : ℝ) (hp : 2 < p) (hαlower : 1/p < α) (hαupper : α < 1/2) (hA : 0 ≤ A)
    (hprofile : ∀ t : ℝ, 1 ≤ t →
      -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal ≤ A * t^(-p)) :
    dirichletEigenvalue n (bridgeProfileOpenDomain n D α hαupper) ≤
      ENNReal.ofReal (8*(A/(1-(2 : ℝ)^(1-α*p))) + 4*(n : ℝ)*Real.log 2) := by
  let U := bridgeProfileOpenDomain n D α hαupper
  have hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))) := by
    change Convex ℝ ((2*bridgeRadius α) • interior D)
    exact hconvex.interior.smul (2*bridgeRadius α)
  have hzeroU : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))) :=
    ⟨0, hzero, smul_zero _⟩
  have hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))) :=
    (hcompact.isBounded.subset interior_subset).smul₀ (2*bridgeRadius α)
  have hunit := bridgeSeriesSurvival_probability_lower n D hcompact hconvex hzero
    p α A hp hαlower hαupper hA hprofile
  have hunit' : ENNReal.ofReal (Real.exp (-(A/(1-(2 : ℝ)^(1-α*p))))) ≤
      bridgeSeriesLaw n (bridgeBrownianSurvivalSet n U) := by
    change ENNReal.ofReal (Real.exp (-(A/(1-(2 : ℝ)^(1-α*p))))) ≤
      bridgeSeriesLaw n {f | ∀ t : Icc (0 : ℝ) 1, f t ∈ (2*bridgeRadius α) • interior D}
    simpa only [bridgeSeriesSurvivalEvent, neg_div] using hunit
  exact bridge_dirichletEigenvalue_le_unit_survival n U hconv hzeroU hbounded _ hunit'

end AffineFKProof
