module

public import AffineFK.GaussianSmoothingIsotropyMoments

/-!
# Actual isotropy preserved by normalized Gaussian smoothing

Literal input coordinate means and raw second moments imply the literal
output moments on the actual affine product-image law. Coordinate L2 and
all output L1 pairings are derived. The explicit smoothed density is
identified with that same measure, without assuming output isotropy.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem gaussianSmoothing_map_isotropy (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (∀ i : Fin n,
      MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i)
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), x i
        ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) = 0) ∧
    (∀ i j : Fin n,
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * x j)
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
        ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) =
          if i = j then (1 : ℝ) else 0) := by
  let μ := ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Measurable W := by fun_prop
  let : IsProbabilityMeasure (μ.map W) := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hxi (i : Fin n) : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (μ.map W) := by
    have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by fun_prop
    exact (memLp_map_measure_iff hc.aestronglyMeasurable hW.aemeasurable).mpr
      (gaussianSmoothing_product_coordinate_memLp n ν hsecond a b i)
  refine ⟨?_, ?_⟩
  · intro i
    refine ⟨hxi i, (hxi i).integrable (by norm_num), ?_⟩
    calc
      _ = ∫ p, (W p) i ∂μ := integral_map hW.aemeasurable
        (show Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) from by fun_prop).aestronglyMeasurable
      _ = 0 := (gaussianSmoothing_product_coordinate_mean n ν hmean hsecond a b i).2
  · intro i j
    refine ⟨(hxi i).integrable_mul (hxi j), ?_⟩
    calc
      _ = ∫ p, (W p) i * (W p) j ∂μ := integral_map hW.aemeasurable
        (show Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i * x j) from by fun_prop).aestronglyMeasurable
      _ = (a ^ 2 + b ^ 2) * (if i = j then (1 : ℝ) else 0) :=
        (gaussianSmoothing_product_coordinate_second n ν hmean hsecond a b i j).2
      _ = _ := by rw [hab, one_mul]

theorem gaussianSmoothing_density_isotropy (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (a b : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    (∀ i : Fin n,
      MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i) (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), x i ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) = 0) ∧
    (∀ i j : Fin n,
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * x j) (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) =
        if i = j then (1 : ℝ) else 0) := by
  simpa only [gaussianSmoothingDensity_law n ν a b hb] using
    gaussianSmoothing_map_isotropy n ν hmean hsecond a b hab

theorem gaussianSmoothing_isotropy_with_law (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (a b : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2) =
      densityMeasure n (gaussianSmoothingDensity n ν a b) ∧
    (∀ i : Fin n,
      MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i)
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), x i
        ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) = 0) ∧
    (∀ i j : Fin n,
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * x j)
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
        ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) =
          if i = j then (1 : ℝ) else 0) := by
  have h := gaussianSmoothing_map_isotropy n ν hmean hsecond a b hab
  exact ⟨gaussianSmoothingDensity_law n ν a b hb, h.1, h.2⟩

end AffineFKProof
