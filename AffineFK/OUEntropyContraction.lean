module

public import AffineFK.OrnsteinUhlenbeckScales
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Tactic

/-!
# Actual Gaussian invariance and extended OU entropy contraction

The Gaussian characteristic-function and the extended-valued KL chain-rule
and data-processing proofs are reused from Mathlib (Rémy Degenne,
Etienne Marion and Lorenzo Luccioli; Apache-2.0). No finite-entropy
assumption is made, and every pushforward map is proved measurable.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

def ouInitialLaw (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (t : ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
    (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)

instance ouInitialLaw_isProbabilityMeasure (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (t : ℝ) :
    IsProbabilityMeasure (ouInitialLaw n ν t) := by
  unfold ouInitialLaw
  infer_instance

theorem ouInitial_gaussian_affine_invariant (n : ℕ) (a b : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2) = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let L : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    a • ContinuousLinearMap.fst ℝ _ _ + b • ContinuousLinearMap.snd ℝ _ _
  change ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
    (stdGaussian (EuclideanSpace ℝ (Fin n)))).map L = _
  apply Measure.ext_of_charFunDual
  ext ℓ
  rw [charFunDual_map, charFunDual_prod]
  have hfst : (ℓ.comp L).comp (ContinuousLinearMap.inl ℝ _ _) = a • ℓ := by
    ext x
    simp [L]
  have hsnd : (ℓ.comp L).comp (ContinuousLinearMap.inr ℝ _ _) = b • ℓ := by
    ext x
    simp [L]
  rw [hfst, hsnd, charFunDual_stdGaussian, charFunDual_stdGaussian,
    charFunDual_stdGaussian, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    ← Complex.exp_add]
  congr 1
  have he : -(|a| * ‖ℓ‖) ^ 2 / 2 + -(|b| * ‖ℓ‖) ^ 2 / 2 = -‖ℓ‖ ^ 2 / 2 := by
    rw [mul_pow, mul_pow, sq_abs, sq_abs]
    nlinarith [hab]
  exact_mod_cast he

theorem ouInitial_klDiv_prod_right
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : Measure Y) [IsProbabilityMeasure η] :
    klDiv (μ.prod η) (ν.prod η) = klDiv μ ν := by
  simpa only [Measure.compProd_const] using klDiv_compProd_left μ ν (Kernel.const X η)

theorem ouInitial_affine_entropy_contraction (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    klDiv ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h := klDiv_map_le (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
    ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n))))
    (g := fun p => a • p.1 + b • p.2) (by fun_prop)
  rw [ouInitial_gaussian_affine_invariant n a b hab, ouInitial_klDiv_prod_right] at h
  exact h

theorem ouInitial_entropy_contraction (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (t : ℝ) (ht : 0 ≤ t) :
    klDiv (ouInitialLaw n ν t) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have he : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  apply ouInitial_affine_entropy_contraction
  rw [ou_exponential_power, Real.sq_sqrt (sub_nonneg.mpr he)]
  simp

end AffineFKProof
