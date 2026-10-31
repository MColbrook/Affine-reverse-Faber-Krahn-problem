module

public import AffineFK.GaussianReferenceScore
public import AffineFK.GaussianSmoothingRegularity

/-!
# The actual relative Gaussian score of a smoothed probability law

The positive smooth density ratio reconstructs the actual law and agrees
almost everywhere with its Radon--Nikodym derivative. The score is the
gradient of its logarithm. Identification with a weak field is almost
everywhere, without assuming square integrability of this gradient.

The proof composes the separately checked smoothing, Radon--Nikodym and
distributional uniqueness results. Their Mathlib attributions are retained
in the imported modules. No derivative of an arbitrary RN version is used.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ContDiff Distributions RealInnerProductSpace

def gaussianSmoothingRelativeDensity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  gaussianSmoothingDensity n ν a b x / standardGaussianDensity n x

def gaussianSmoothingScore (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  gradient (fun y => Real.log (gaussianSmoothingRelativeDensity n ν a b y)) x

theorem gaussianSmoothingRelativeDensity_properties (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    ContDiff ℝ ∞ (gaussianSmoothingRelativeDensity n ν a b) ∧
    (∀ x, 0 < gaussianSmoothingRelativeDensity n ν a b x) ∧
    (stdGaussian (EuclideanSpace ℝ (Fin n))).withDensity
      (fun x => ENNReal.ofReal (gaussianSmoothingRelativeDensity n ν a b x)) =
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2) ∧
    ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)).rnDeriv
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
      =ᵐ[stdGaussian (EuclideanSpace ℝ (Fin n))]
        (fun x => ENNReal.ofReal (gaussianSmoothingRelativeDensity n ν a b x)) := by
  have hρ := gaussianSmoothingDensity_smooth n ν a b
  have hρpos := gaussianSmoothingDensity_pos n ν a b hb
  have hlaw := gaussianSmoothingDensity_law n ν a b hb
  refine ⟨gaussian_relative_density_smooth n _ hρ,
    gaussian_relative_density_pos n _ hρpos, ?_, ?_⟩
  · exact (gaussian_relative_density_withDensity n _ hρ.continuous).trans hlaw.symm
  · rw [hlaw]
    exact gaussian_relative_density_rnDeriv n _ hρ.continuous

theorem gaussianSmoothingScore_eq_density_score (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    gaussianSmoothingScore n ν a b =
      gaussianRelativeScore n (gaussianSmoothingDensity n ν a b) := by
  funext x
  exact gradient_log_gaussian_relative_density n _
    (gaussianSmoothingDensity_smooth n ν a b)
    (gaussianSmoothingDensity_pos n ν a b hb) x

theorem gaussianSmoothingScore_identified_by_weak_identity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : MemLp r 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)))
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪r x, F x⟫ ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) =
      ∫ x, ⟪x, F x⟫ - vectorDivergence n F x
        ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) :
    r =ᵐ[(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)] gaussianSmoothingScore n ν a b ∧
    MemLp (gaussianSmoothingScore n ν a b) 2
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
    (∫ x, ‖gaussianSmoothingScore n ν a b x‖ ^ 2
      ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) =
      ∫ x, ‖r x‖ ^ 2 ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2) := by
  have hlaw := gaussianSmoothingDensity_law n ν a b hb
  letI : IsProbabilityMeasure (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
    rw [← hlaw]
    infer_instance
  rw [hlaw] at hr hweak ⊢
  rw [gaussianSmoothingScore_eq_density_score n ν a b hb]
  exact gaussianRelativeScore_identified_by_weak_identity n _
    (gaussianSmoothingDensity_smooth n ν a b)
    (gaussianSmoothingDensity_pos n ν a b hb) r hr hweak

end AffineFKProof
