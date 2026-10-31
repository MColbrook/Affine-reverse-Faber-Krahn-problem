module

public import AffineFK.OUEntropyContraction
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# OU smoothing commutes with normalized convolution

Characteristic-function uniqueness proves equality of the actual product
pushforwards. No input density, moment, smoothness or information is needed.
Mathlib characteristic-function proofs are reused with their original
attribution (Etienne Marion and the characteristic-function contributors).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem charFun_affine_product (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (a b : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    charFun ((ν.prod η).map (fun p => a • p.1 + b • p.2)) v =
      charFun ν (a • v) * charFun η (b • v) := by
  have hlaw : ((ν.map (fun x => a • x)).prod (η.map (fun x => b • x))).map
      (fun p => p.1 + p.2) = (ν.prod η).map (fun p => a • p.1 + b • p.2) := by
    rw [Measure.map_prod_map ν η (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [← hlaw, charFun_map_add_prod_eq_mul, Pi.mul_apply,
    charFun_map_smul, charFun_map_smul]

theorem charFun_ouInitialLaw (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    charFun (ouInitialLaw n ν t) v =
      charFun ν (Real.exp (-t) • v) *
        Complex.exp (-(‖Real.sqrt (1 - Real.exp (-2 * t)) • v‖ ^ 2 : ℂ) / 2) := by
  rw [ouInitialLaw, charFun_affine_product, charFun_stdGaussian]

theorem ouInitialLaw_normalized_convolution (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (t : ℝ) :
    ouInitialLaw n ((ν.prod η).map (fun p => a • p.1 + b • p.2)) t =
      ((ouInitialLaw n ν t).prod (ouInitialLaw n η t)).map
        (fun p => a • p.1 + b • p.2) := by
  apply Measure.ext_of_charFun
  funext v
  rw [charFun_ouInitialLaw, charFun_affine_product,
    charFun_affine_product, charFun_ouInitialLaw, charFun_ouInitialLaw]
  have ha : a • (Real.exp (-t) • v) = Real.exp (-t) • (a • v) := by
    rw [smul_smul, smul_smul, mul_comm a]
  have hb : b • (Real.exp (-t) • v) = Real.exp (-t) • (b • v) := by
    rw [smul_smul, smul_smul, mul_comm b]
  rw [ha, hb]
  have hn : -(‖Real.sqrt (1 - Real.exp (-2 * t)) • v‖ ^ 2) / 2 =
      -(‖Real.sqrt (1 - Real.exp (-2 * t)) • (a • v)‖ ^ 2) / 2 +
      -(‖Real.sqrt (1 - Real.exp (-2 * t)) • (b • v)‖ ^ 2) / 2 := by
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    linear_combination (Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 * ‖v‖ ^ 2 / 2) * hab
  have he : Complex.exp (-(‖Real.sqrt (1 - Real.exp (-2 * t)) • v‖ ^ 2 : ℂ) / 2) =
      Complex.exp (-(‖Real.sqrt (1 - Real.exp (-2 * t)) • (a • v)‖ ^ 2 : ℂ) / 2) *
      Complex.exp (-(‖Real.sqrt (1 - Real.exp (-2 * t)) • (b • v)‖ ^ 2 : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    exact_mod_cast hn
  rw [he]
  ring

end AffineFKProof
