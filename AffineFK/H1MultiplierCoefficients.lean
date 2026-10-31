module

public import AffineFK.L2CoefficientField
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Actual L2 coefficient operators for the smooth H1 product rule

The value multiplier, gradient multiplier and cross term are bounded
operators on infinite-volume Lebesgue L2. Smoothness and the two genuine
pointwise bounds are their only analytic hypotheses.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory InnerProductSpace ContinuousLinearMap
open scoped ContDiff

def h1ScalarCoefficient (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C : ℝ) (hb : ∀ x, ‖m x‖ ≤ C) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  l2CoefficientField n (fun x => toSpanSingleton ℝ (m x))
    (((toSpanSingletonLIE ℝ ℝ).continuous.comp hm.continuous).stronglyMeasurable)
    C (fun x => by simpa only [norm_toSpanSingleton] using hb x)

theorem h1ScalarCoefficient_coe (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C : ℝ) (hb : ∀ x, ‖m x‖ ≤ C)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    h1ScalarCoefficient n m hm C hb f =ᵐ[volume] fun x => m x * f x := by
  simpa only [h1ScalarCoefficient, toSpanSingleton_apply, smul_eq_mul, mul_comm] using
    l2CoefficientField_coe n (fun x => toSpanSingleton ℝ (m x))
      (((toSpanSingletonLIE ℝ ℝ).continuous.comp hm.continuous).stronglyMeasurable)
      C (fun x => by simpa only [norm_toSpanSingleton] using hb x) f

theorem h1VectorCoefficient_bound (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : ℝ) (hb : ∀ x, ‖m x‖ ≤ C) (x : EuclideanSpace ℝ (Fin n)) :
    ‖m x • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ C := by
  calc
    _ ≤ ‖m x‖ * ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ := norm_smul_le _ _
    _ ≤ ‖m x‖ * 1 := mul_le_mul_of_nonneg_left norm_id_le (norm_nonneg _)
    _ ≤ C := by simpa only [mul_one] using hb x

def h1VectorCoefficient (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C : ℝ) (hb : ∀ x, ‖m x‖ ≤ C) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  l2CoefficientField n (fun x => m x • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    ((hm.continuous.smul continuous_const).stronglyMeasurable)
    C (h1VectorCoefficient_bound n m C hb)

theorem h1VectorCoefficient_coe (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C : ℝ) (hb : ∀ x, ‖m x‖ ≤ C)
    (g : Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    h1VectorCoefficient n m hm C hb g =ᵐ[volume] fun x => m x • g x := by
  simpa only [h1VectorCoefficient, smul_apply, id_apply] using
    l2CoefficientField_coe n (fun x => m x • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      ((hm.continuous.smul continuous_const).stronglyMeasurable)
      C (h1VectorCoefficient_bound n m C hb) g

theorem h1_gradient_continuous (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) : Continuous (gradient m) :=
  (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp (hm.continuous_fderiv (by simp))

def h1CrossCoefficient (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C : ℝ) (hb : ∀ x, ‖gradient m x‖ ≤ C) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  l2CoefficientField n (fun x => toSpanSingleton ℝ (gradient m x))
    (((toSpanSingletonLIE ℝ (EuclideanSpace ℝ (Fin n))).continuous.comp
      (h1_gradient_continuous n m hm)).stronglyMeasurable)
    C (fun x => by simpa only [norm_toSpanSingleton] using hb x)

theorem h1CrossCoefficient_coe (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C : ℝ) (hb : ∀ x, ‖gradient m x‖ ≤ C)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    h1CrossCoefficient n m hm C hb f =ᵐ[volume] fun x => f x • gradient m x := by
  simpa only [h1CrossCoefficient, toSpanSingleton_apply] using
    l2CoefficientField_coe n (fun x => toSpanSingleton ℝ (gradient m x))
      (((toSpanSingletonLIE ℝ (EuclideanSpace ℝ (Fin n))).continuous.comp
        (h1_gradient_continuous n m hm)).stronglyMeasurable)
      C (fun x => by simpa only [norm_toSpanSingleton] using hb x) f

end AffineFKProof
