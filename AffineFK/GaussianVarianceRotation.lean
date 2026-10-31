module

public import AffineFK.PoincareConvolutionAverage
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# The actual Gaussian rotation law and gradient correlation bound

Characteristic-function uniqueness proves that a normalized real linear
combination of two independent standard Gaussian vectors is standard
Gaussian. This result and the Hilbert norm identity give the exact
correlation bound needed for Gaussian variance interpolation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace ENNReal

theorem gaussianVariance_mix_law (n : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2) =
        stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hlaw : ((γ.map (fun x => a • x)).prod (γ.map (fun x => b • x))).map
      (fun p => p.1 + p.2) = (γ.prod γ).map (fun p => a • p.1 + b • p.2) := by
    rw [Measure.map_prod_map γ γ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  change (γ.prod γ).map _ = γ
  rw [← hlaw]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_add_prod_eq_mul, Pi.mul_apply, charFun_map_smul, charFun_map_smul,
    charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have hn : -(‖a • t‖ ^ 2) / 2 + -(‖b • t‖ ^ 2) / 2 = -(‖t‖ ^ 2) / 2 := by
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    nlinarith [hab]
  exact_mod_cast hn

theorem gaussianVariance_gradient_correlation_le (n : ℕ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ⟪gradient f p.1, gradient f (a • p.1 + b • p.2)⟫
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, ‖gradient f x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let μ := γ.prod γ
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : HasLaw W γ μ := ⟨by fun_prop, gaussianVariance_mix_law n a b hab⟩
  have hgrad : MemLp (gradient f) 2 γ := by
    apply (Lp.memLp (testFunctionToL2 γ (testFunctionGradient f))).ae_eq
    exact (testFunctionToL2_coe γ _).trans (Eventually.of_forall fun x => testFunctionGradient_apply _ x)
  have hU : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      gradient f p.1) 2 μ := hgrad.comp_fst γ
  have hV : MemLp (fun p => gradient f (W p)) 2 μ := hW.memLp_fun_comp hgrad
  have hi : Integrable (fun p => ⟪gradient f p.1, gradient f (W p)⟫) μ :=
    memLp_one_iff_integrable.mp ((innerSL ℝ).memLp_of_bilin 1 hU hV)
  have hu : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖gradient f p.1‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU
  have hv : Integrable (fun p => ‖gradient f (W p)‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hV
  have hh : (∫ p, 2 * ⟪gradient f p.1, gradient f (W p)⟫ ∂μ) ≤
      ∫ p, ‖gradient f p.1‖ ^ 2 + ‖gradient f (W p)‖ ^ 2 ∂μ := by
    apply integral_mono (hi.const_mul 2) (hu.add hv)
    intro p
    change 2 * ⟪gradient f p.1, gradient f (W p)⟫ ≤
      ‖gradient f p.1‖ ^ 2 + ‖gradient f (W p)‖ ^ 2
    have hs := norm_sub_sq_real (gradient f p.1) (gradient f (W p))
    nlinarith [sq_nonneg ‖gradient f p.1 - gradient f (W p)‖]
  rw [integral_const_mul, integral_add hu hv] at hh
  have hfirst : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖gradient f p.1‖ ^ 2 ∂μ) = ∫ x, ‖gradient f x‖ ^ 2 ∂γ := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := γ) (ν := γ) (fun x => ‖gradient f x‖ ^ 2))
  have hsecond : (∫ p, ‖gradient f (W p)‖ ^ 2 ∂μ) = ∫ x, ‖gradient f x‖ ^ 2 ∂γ :=
    hW.integral_comp ((memLp_two_iff_integrable_sq_norm hgrad.aestronglyMeasurable).mp hgrad).aestronglyMeasurable
  rw [hfirst, hsecond] at hh
  nlinarith

end AffineFKProof
