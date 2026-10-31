module

public import AffineFK.SteinTensorAssembly
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Reflection of smooth tests and of the component identity

Reflection reverses first partials and preserves second partials. Under an
even measure the scalar Stein functional changes sign. These identities
allow antisymmetrisation of the constructed tensor without increasing its
energy.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

def reflectedTest
    (n : ℕ) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  scaledTestFunction (-1) (by norm_num) φ

theorem reflectedTest_apply
    (n : ℕ) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) : reflectedTest n φ x = φ (-x) := by
  simp [reflectedTest, scaledTestFunction_apply]

theorem reflectedTest_gradient
    (n : ℕ) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (reflectedTest n φ) x = -gradient φ (-x) := by
  simpa [reflectedTest] using gradient_scaledTestFunction (-1) (by norm_num) φ x

theorem partialTest_neg
    (n : ℕ) (j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n j (-φ) = -partialTest n j φ := by
  unfold partialTest
  rw [map_neg, map_neg]

theorem partialTest_reflected
    (n : ℕ) (j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n j (reflectedTest n φ) = -reflectedTest n (partialTest n j φ) := by
  ext x
  rw [partialTest_apply, reflectedTest_gradient]
  simp [reflectedTest_apply, partialTest_apply]

theorem partialTest_second_reflected
    (n : ℕ) (j k : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n k (partialTest n j (reflectedTest n φ)) =
      reflectedTest n (partialTest n k (partialTest n j φ)) := by
  rw [partialTest_reflected, partialTest_neg, partialTest_reflected, neg_neg]

theorem stein_component_left_reflected
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [Measure.IsNegInvariant ν]
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, x i * reflectedTest n φ x ∂ν) -
      (∫ x, partialTest n i (reflectedTest n φ) x ∂ν) =
        -((∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν)) := by
  have hfirst : (∫ x, x i * reflectedTest n φ x ∂ν) = -(∫ x, x i * φ x ∂ν) := by
    have h := integral_neg_eq_self
      (fun x : EuclideanSpace ℝ (Fin n) => x i * φ (-x)) ν
    simp only [neg_neg, PiLp.neg_apply, neg_mul, integral_neg] at h
    simpa only [reflectedTest_apply] using h.symm
  have hsecond : (∫ x, partialTest n i (reflectedTest n φ) x ∂ν) =
      -(∫ x, partialTest n i φ x ∂ν) := by
    rw [partialTest_reflected]
    change (∫ x, -(reflectedTest n (partialTest n i φ) x) ∂ν) = _
    simp only [reflectedTest_apply, integral_neg]
    rw [integral_neg_eq_self (partialTest n i φ) ν]
  rw [hfirst, hsecond]
  ring

theorem tensor_contraction_reflected_integral
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [Measure.IsNegInvariant ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, tensorPartialContraction n T i (reflectedTest n φ) x ∂ν) =
      ∫ x, tensorPartialContraction n (fun y => T (-y)) i φ x ∂ν := by
  rw [← integral_neg_eq_self (tensorPartialContraction n T i (reflectedTest n φ)) ν]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [tensorPartialContraction, partialTest_second_reflected,
    reflectedTest_apply, neg_neg]

end AffineFKProof
