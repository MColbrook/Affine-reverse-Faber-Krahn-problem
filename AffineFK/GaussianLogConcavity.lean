module

public import AffineFK.LogConcaveDensityCalculus
public import AffineFK.StandardGaussianDensity

/-!
# Log-concavity of the actual standard Gaussian density

The usual exponential characterization is proved directly from the
weighted concavity inequality. The Gaussian coordinate proof uses the
nonnegative square of the difference; finite products preserve the same
pointwise definition. Mathlib's exponential and Gaussian density APIs
are reused with their Apache-2.0 contributor attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem logConcaveDensity_exp {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (V : E → ℝ)
    (hV : ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ x y,
      (1 - t) * V x + t * V y ≤ V ((1 - t) • x + t • y)) :
    LogConcaveDensity (fun x => ENNReal.ofReal (Real.exp (V x))) := by
  intro t ht ht1 x y
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg _ _),
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
    simpa only [mul_comm] using hV t ht ht1 x y))
  all_goals positivity

theorem logConcaveDensity_const {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (c : ℝ≥0∞) : LogConcaveDensity (fun _ : E => c) := by
  intro t ht ht1 x y
  rw [← ENNReal.rpow_add_of_nonneg (1 - t) t (sub_nonneg.mpr ht1) ht]
  simp

theorem logConcaveDensity_gaussianPDFReal :
    LogConcaveDensity (fun x : ℝ => ENNReal.ofReal (gaussianPDFReal 0 1 x)) := by
  have hexp : LogConcaveDensity (fun x : ℝ => ENNReal.ofReal (Real.exp (-(x ^ 2) / 2))) := by
    apply logConcaveDensity_exp
    intro t ht ht1 x y
    simp only [smul_eq_mul]
    have hp : 0 ≤ t * (1 - t) * (x - y) ^ 2 :=
      mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ht1)) (sq_nonneg _)
    nlinarith
  have hprod := logConcaveDensity_mul
    (fun _ : ℝ => ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹)) _
    (logConcaveDensity_const _) hexp
  simpa only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))] using hprod

theorem logConcaveDensity_finset_prod {E ι : Type*}
    [AddCommMonoid E] [Module ℝ E] (s : Finset ι) (f : ι → E → ℝ≥0∞)
    (hf : ∀ i ∈ s, LogConcaveDensity (f i)) :
    LogConcaveDensity (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (logConcaveDensity_const (E := E) 1)
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      logConcaveDensity_mul (f i) (fun x => ∏ j ∈ s, f j x)
        (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem logConcaveDensity_standardGaussian (n : ℕ) :
    LogConcaveDensity (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (standardGaussianDensity n x)) := by
  have hcoord (i : Fin n) : LogConcaveDensity
      (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (gaussianPDFReal 0 1 (x i))) := by
    intro t ht ht1 x y
    exact logConcaveDensity_gaussianPDFReal t ht ht1 (x i) (y i)
  have hp := logConcaveDensity_finset_prod Finset.univ _ (fun i _ => hcoord i)
  simpa only [standardGaussianDensity,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 _)] using hp

end AffineFKProof
