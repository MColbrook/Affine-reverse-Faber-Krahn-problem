module

public import AffineFK.GaussianSecondDensityRatioCalculus
public import AffineFK.GaussianSecondDensityRatioField
public import AffineFK.GaussianSmoothingRegularity

/-!
# Actual second-density ratios of arbitrary Gaussian-smoothed laws

The conditional field is identified against all compact smooth tests
with the actual second derivative divided by the actual positive smooth
density. L2 membership and the exact bound follow after identification.
There is no initial density or moment hypothesis.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

theorem gaussianSmoothing_secondDensityRatio_conditional (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i j : Fin n) (a b : ℝ) (hb : 0 < b) :
    ∃ q : EuclideanSpace ℝ (Fin n) → ℝ,
      StronglyMeasurable q ∧
      MemLp q 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        q (a • p.1 + b • p.2) = (b⁻¹) ^ 2 * condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • z.1 + b • z.2))
          (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
          (fun z => z.2 i * z.2 j - if i = j then 1 else 0) p) ∧
      (q =ᵐ[(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)]
          secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j) ∧
      MemLp (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j) 2
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) ∧
      Integrable (fun x => (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x) ^ 2)
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) ∧
      (∫ x, (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x) ^ 2
        ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) ≤ (b⁻¹) ^ 4 * (if i = j then (2 : ℝ) else 1) := by
  let μ := ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Measurable W := by fun_prop
  have : IsProbabilityMeasure (μ.map W) := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let ρ := gaussianSmoothingDensity n ν a b
  have hlaw : μ.map W = densityMeasure n ρ := gaussianSmoothingDensity_law n ν a b hb
  have : IsProbabilityMeasure (densityMeasure n ρ) := by rw [← hlaw]; infer_instance
  obtain ⟨q, hq, hq2, hrep, hbound, hweak⟩ := gaussianSmoothing_second_density_field n ν i j a b hb.ne'
  have hqρ : MemLp q 2 (densityMeasure n ρ) := by rw [← hlaw]; exact hq2
  have hweakρ (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
      (∫ x, q x * φ x ∂densityMeasure n ρ) =
        ∫ x, partialTest n i (partialTest n j φ) x ∂densityMeasure n ρ := by
    rw [← hlaw]
    exact (hweak φ).2.2
  have hid := secondDensityRatio_identified_by_test_identity n ρ
    (gaussianSmoothingDensity_smooth n ν a b) (gaussianSmoothingDensity_pos n ν a b hb)
    i j q hqρ hweakρ
  have heq : q =ᵐ[μ.map W] secondDensityRatio n ρ i j := by simpa only [← hlaw] using hid.1
  have hratio : MemLp (secondDensityRatio n ρ i j) 2 (μ.map W) := hq2.ae_eq heq
  have hratioL1 : Integrable (fun x => (secondDensityRatio n ρ i j x) ^ 2) (μ.map W) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hratio.integrable_norm_pow (by norm_num)
  refine ⟨q, hq, hq2, hrep, heq, hratio, hratioL1, ?_⟩
  calc
    _ = ∫ x, (q x) ^ 2 ∂μ.map W := integral_congr_ae (heq.symm.fun_comp fun z => z ^ 2)
    _ ≤ _ := hbound

theorem gaussianSmoothing_secondDensityRatio_memLp (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i j : Fin n) (a b : ℝ) (hb : 0 < b) :
    MemLp (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j) 2
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
    Integrable (fun x => (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x) ^ 2)
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
    (∫ x, (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x) ^ 2
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) ≤
        (b⁻¹) ^ 4 * (if i = j then (2 : ℝ) else 1) := by
  obtain ⟨q, _hq, _hq2, _hrep, _heq, hratio, hi, hbound⟩ :=
    gaussianSmoothing_secondDensityRatio_conditional n ν i j a b hb
  simpa only [gaussianSmoothingDensity_law n ν a b hb] using And.intro hratio (And.intro hi hbound)

end AffineFKProof
