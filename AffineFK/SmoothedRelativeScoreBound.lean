module

public import AffineFK.GaussianSmoothedScore
public import AffineFK.SmoothedSteinField
public import AffineFK.OrnsteinUhlenbeckScales

/-!
# Conditional representation and information bound for the actual score

The conditional field already constructed from the original Stein tensor
equals the logarithmic relative score almost everywhere on the actual
smoothed law. Pulling this equality back gives an almost-everywhere
conditional representation, with the exact Gaussian tensor energy bound.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem smoothed_stein_relative_score (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) =
        ∫ x, vectorHessianContraction n T F x ∂ν)
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    MemLp (gaussianSmoothingScore n ν a b) 2
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
    (∀ᵐ p ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))),
      gaussianSmoothingScore n ν a b (a • p.1 + b • p.2) =
        (a ^ 3 / b ^ 2) • condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • q.1 + b • q.2))
          (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
          (fun q => gaussianHermiteContraction n (T q.1) q.2) p) ∧
    (∫ x, ‖gaussianSmoothingScore n ν a b x‖ ^ 2
      ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ≤
      (2 * a ^ 6 / b ^ 4) * (∫ u, ‖T u‖ ^ 2 ∂ν) := by
  obtain ⟨r, _, hr, hrep, hbound, hweak⟩ :=
    smoothed_stein_vector_field n ν hxi T hT hidentity a b ha hb.ne' hab
  obtain ⟨heq, hscore, henergy⟩ :=
    gaussianSmoothingScore_identified_by_weak_identity n ν a b hb r hr
      (fun F => (hweak F).2.2)
  refine ⟨hscore, ?_, henergy.trans_le hbound⟩
  have hW : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      a • p.1 + b • p.2) := by fun_prop
  filter_upwards [ae_of_ae_map hW.aemeasurable heq] with p hp
  exact hp.symm.trans (hrep p)

theorem OU_stein_relative_score_information_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) =
        ∫ x, vectorHessianContraction n T F x ∂ν)
    (t : ℝ) (ht : 0 < t) :
    MemLp (gaussianSmoothingScore n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))) 2
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ∧
    (∫ x, ‖gaussianSmoothingScore n ν (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t))) x‖ ^ 2
      ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ≤
      (2 * Real.exp (-6 * t) / (1 - Real.exp (-2 * t)) ^ 2) *
        (∫ u, ‖T u‖ ^ 2 ∂ν) := by
  have hd := ou_smoothing_scale_domain t ht
  have h := smoothed_stein_relative_score n ν hxi T hT hidentity
    (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) hd.1.ne' hd.2.1 hd.2.2
  refine ⟨h.1, ?_⟩
  simpa only [(ou_smoothing_scale_coefficients t ht).2] using h.2.2

end AffineFKProof
