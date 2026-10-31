module

public import AffineFK.LogConcaveDensityCalculus
public import Mathlib.Analysis.Convex.Function

/-!
# The logarithm of a positive log-concave density

The extended nonnegative definition implies ordinary real concavity of
the logarithm on the full vector space. Positivity is explicit and all
real logarithms are applied only to positive values.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem logConcaveDensity_concaveOn_log {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (ρ : E → ℝ) (hρpos : ∀ x, 0 < ρ x)
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (ρ x))) :
    ConcaveOn ℝ Set.univ (fun x => Real.log (ρ x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have haeq : 1 - b = a := by linarith
  have h := hlc b hb hb1 x y
  rw [haeq] at h
  have hreal : ρ x ^ a * ρ y ^ b ≤ ρ (a • x + b • y) := by
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (hρpos x).le, ENNReal.toReal_ofReal (hρpos y).le,
      ENNReal.toReal_ofReal (hρpos (a • x + b • y)).le] using hmono
  have hlog := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos (hρpos x) _) (Real.rpow_pos_of_pos (hρpos y) _)) hreal
  rw [Real.log_mul (Real.rpow_pos_of_pos (hρpos x) _).ne'
    (Real.rpow_pos_of_pos (hρpos y) _).ne', Real.log_rpow (hρpos x), Real.log_rpow (hρpos y)] at hlog
  exact hlog

end AffineFKProof
