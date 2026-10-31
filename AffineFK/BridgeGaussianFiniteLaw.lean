module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Tactic.Ring

/-!
# Equality of genuine finite Gaussian laws from their means and covariances

This uses Mathlib's actual Gaussian characteristic-function formula and
injectivity of characteristic functions on finite-dimensional spaces.
No equality of the desired laws is supplied as a premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

theorem bridge_gaussian_finite_law_ext {Ω Λ ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Λ] [Fintype ι] (P : Measure Ω) (Q : Measure Λ)
    (X : Ω → ι → ℝ) (Y : Λ → ι → ℝ) (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y Q)
    (hmean : ∀ i, (∫ ω, X ω i ∂P) = ∫ ω, Y ω i ∂Q)
    (hcov : ∀ i j, cov[fun ω => X ω i, fun ω => X ω j; P] =
      cov[fun ω => Y ω i, fun ω => Y ω j; Q]) : P.map X = Q.map Y := by
  classical
  letI := hX.isProbabilityMeasure
  letI := hY.isProbabilityMeasure
  letI := hX.isGaussian_map
  letI := hY.isGaussian_map
  apply Measure.ext_of_charFunDual
  funext L
  rw [hX.charFunDual_map_eq, hY.charFunDual_map_eq]
  let a : ι → ℝ := fun i => L (Pi.single i 1)
  have hL (v : ι → ℝ) : L v = ∑ i, a i * v i := by
    have hv : (∑ i : ι, v i • Pi.single i (1 : ℝ)) = v := by
      ext j
      simp [Pi.single_apply]
    calc
      L v = L (∑ i : ι, v i • Pi.single i (1 : ℝ)) := congrArg L hv.symm
      _ = ∑ i, a i * v i := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp [a, mul_comm]
  have hXP (i : ι) : MemLp (fun ω => a i * X ω i) 2 P := (hX.eval i).memLp_two.const_mul _
  have hYQ (i : ι) : MemLp (fun ω => a i * Y ω i) 2 Q := (hY.eval i).memLp_two.const_mul _
  have hm : (∫ ω, L (X ω) ∂P) = ∫ ω, L (Y ω) ∂Q := by
    simp_rw [hL]
    rw [integral_finsetSum Finset.univ (fun i _ => (hXP i).integrable (by norm_num)),
      integral_finsetSum Finset.univ (fun i _ => (hYQ i).integrable (by norm_num))]
    simp_rw [integral_const_mul, hmean]
  have hv : Var[fun ω => L (X ω); P] = Var[fun ω => L (Y ω); Q] := by
    simp_rw [hL]
    rw [variance_fun_sum hXP, variance_fun_sum hYQ]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_const_mul_left, covariance_const_mul_right, hcov]
  change Complex.exp (((∫ ω, L (X ω) ∂P) : ℝ) * Complex.I -
      Var[fun ω => L (X ω); P] / 2) = _
  rw [hm, hv]
  rfl

end AffineFKProof
