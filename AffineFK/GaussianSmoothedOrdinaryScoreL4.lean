module

public import AffineFK.GaussianSmoothedOrdinaryScoreL4Field
public import AffineFK.GaussianSmoothingRegularity
public import AffineFK.OrdinaryWeakScoreSobolevSmooth

/-!
# Actual L4 ordinary score of an arbitrary Gaussian-smoothed law

The explicit positive smooth density is the actual affine Gaussian image
law. Its genuine logarithmic gradient is identified almost everywhere
with the single constructed weak conditional field before its L2 and L4
membership are asserted. No moment, density or score condition is imposed
on the original probability law.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem gaussianSmoothing_ordinaryScore_conditional_L4 (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧
      MemLp r 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      MemLp r 4 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        r (a • p.1 + b • p.2) = (-b⁻¹) • condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • q.1 + b • q.2))
          (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) Prod.snd p) ∧
      (r =ᵐ[(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)]
          gradient (fun x => Real.log (gaussianSmoothingDensity n ν a b x))) ∧
      MemLp (gradient (fun x => Real.log (gaussianSmoothingDensity n ν a b x))) 2
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) ∧
      MemLp (gradient (fun x => Real.log (gaussianSmoothingDensity n ν a b x))) 4
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) ∧
      Integrable (fun x => ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x‖ ^ 4)
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) ∧
      (∫ x, ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x‖ ^ 4
        ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) ≤ (b⁻¹) ^ 4 * ((n : ℝ) * (n + 2)) := by
  let μ := ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Measurable W := by fun_prop
  let : IsProbabilityMeasure (μ.map W) := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let ρ := gaussianSmoothingDensity n ν a b
  have hlaw : μ.map W = densityMeasure n ρ := gaussianSmoothingDensity_law n ν a b hb
  let : IsProbabilityMeasure (densityMeasure n ρ) := by rw [← hlaw]; infer_instance
  obtain ⟨r, hr, hr2, hr4, _hfourL1, hrep, hbound, hweak⟩ :=
    gaussianSmoothing_ordinary_score_field n ν a b hb
  have hrρ : MemLp r 2 (densityMeasure n ρ) := by rw [← hlaw]; exact hr2
  have hweakρ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
      (∫ x, r x i * φ x ∂densityMeasure n ρ) = -(∫ x, partialTest n i φ x ∂densityMeasure n ρ) := by
    rw [← hlaw]
    exact (hweak i φ).2.2
  have hid := ordinaryWeakScore_smooth_identification n ρ (gaussianSmoothingDensity_smooth n ν a b)
    (gaussianSmoothingDensity_pos n ν a b hb) r hrρ hweakρ
  have hident : r =ᵐ[μ.map W] gradient (fun x => Real.log (ρ x)) := by
    simpa only [← hlaw] using hid.1
  have hs2 : MemLp (gradient (fun x => Real.log (ρ x))) 2 (μ.map W) := hr2.ae_eq hident
  have hs4 : MemLp (gradient (fun x => Real.log (ρ x))) 4 (μ.map W) := hr4.ae_eq hident
  refine ⟨r, hr, hr2, hr4, hrep, hident, hs2, hs4, hs4.integrable_norm_pow (by norm_num), ?_⟩
  have heq : (∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 4 ∂μ.map W) =
      ∫ x, ‖r x‖ ^ 4 ∂μ.map W :=
    integral_congr_ae (hident.symm.fun_comp fun z => ‖z‖ ^ 4)
  exact heq.trans_le hbound

theorem gaussianSmoothing_ordinaryScore_memLp_four (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    MemLp (gradient (fun x => Real.log (gaussianSmoothingDensity n ν a b x))) 4
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
    Integrable (fun x => ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x‖ ^ 4)
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
    (∫ x, ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x‖ ^ 4
      ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ≤ (b⁻¹) ^ 4 * ((n : ℝ) * (n + 2)) := by
  obtain ⟨r, _hr, _hr2, _hr4, _hrep, _hid, _hs2, hs4, hsL1, hbound⟩ :=
    gaussianSmoothing_ordinaryScore_conditional_L4 n ν a b hb
  exact ⟨hs4, hsL1, hbound⟩

theorem gaussianSmoothing_ordinaryScore_density_memLp_four (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    MemLp (gradient (fun x => Real.log (gaussianSmoothingDensity n ν a b x))) 4
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
    Integrable (fun x => ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x‖ ^ 4)
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
    (∫ x, ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x‖ ^ 4
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) ≤ (b⁻¹) ^ 4 * ((n : ℝ) * (n + 2)) := by
  simpa only [gaussianSmoothingDensity_law n ν a b hb] using
    gaussianSmoothing_ordinaryScore_memLp_four n ν a b hb

end AffineFKProof
