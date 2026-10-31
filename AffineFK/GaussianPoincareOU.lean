module

public import AffineFK.GaussianPoincare
public import AffineFK.PoincareConvolutionScaled
public import AffineFK.OrnsteinUhlenbeckScales

/-! Exact OU Poincare inheritance, including time zero, from proved Gaussian CP1. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

theorem stdGaussian_OU_poincare (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (t : ℝ) (ht : 0 ≤ t)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ^ 2
      ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ≤
      (Real.exp (-2 * t) * P + 1 - Real.exp (-2 * t)) *
        (∫ x, ‖gradient f x‖ ^ 2 ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) := by
  have hG : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (φ x - ∫ y, φ y ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ^ 2
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
          1 * (∫ x, ‖gradient φ x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    intro φ
    simpa only [one_mul] using stdGaussian_poincare n φ
  have h := poincareConvolution_scaled n ν (stdGaussian (EuclideanSpace ℝ (Fin n))) P 1
    hP0 zero_le_one hP hG (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) f
  have hden : 0 ≤ 1 - Real.exp (-2 * t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have ha2 : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by simpa using ou_exponential_power t 2
  rw [ha2, Real.sq_sqrt hden, mul_one] at h
  simpa only [add_sub_assoc] using h

end AffineFKProof
