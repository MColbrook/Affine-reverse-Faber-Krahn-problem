module

public import AffineFK.OUConvolutionLogConcavity
public import AffineFK.ConvolutionHessianEnergy
public import AffineFK.GaussianHessianL2
public import AffineFK.OrnsteinUhlenbeckScales

/-!
# Genuine positive-time OU convolution Hessian deficit

The output law is identified by proved OU convolution commutation. The
actual output density is positive and smooth, its log-concavity follows
from the genuine Gaussian/product marginal, and all derivative Lp domains
follow from the actual Gaussian conditional fields. Initial densities
need only be measurable and log-concave; no smoothness, information or
moment premise is needed for this positive-time matrix deficit.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff ENNReal Matrix.Norms.L2Operator

theorem ou_normalized_convolution_density_law (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (t : ℝ) (ht : 0 < t) :
    let ρ : Measure (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) → ℝ :=
      fun κ => gaussianSmoothingDensity n κ (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    ((densityMeasure n (ρ ν)).prod (densityMeasure n (ρ η))).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2) =
      densityMeasure n (ρ ((ν.prod η).map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let W : E × E → E := fun p => a • p.1 + b • p.2
  have hW : Measurable W := by dsimp [W]; fun_prop
  let ξ := (ν.prod η).map W
  let : IsProbabilityMeasure ξ := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let ρ : Measure E → E → ℝ :=
    fun κ => gaussianSmoothingDensity n κ (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  have hb := (ou_smoothing_scale_domain t ht).2.1
  have hν : ouInitialLaw n ν t = densityMeasure n (ρ ν) := gaussianSmoothingDensity_law n ν _ _ hb
  have hη : ouInitialLaw n η t = densityMeasure n (ρ η) := gaussianSmoothingDensity_law n η _ _ hb
  have hξ : ouInitialLaw n ξ t = densityMeasure n (ρ ξ) := gaussianSmoothingDensity_law n ξ _ _ hb
  calc
    _ = ((ouInitialLaw n ν t).prod (ouInitialLaw n η t)).map W := by rw [hν, hη]
    _ = ouInitialLaw n ξ t := (ouInitialLaw_normalized_convolution n ν η a b hab t).symm
    _ = _ := hξ

theorem ou_normalized_convolution_hessian_deficit (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f) (hg : Measurable g)
    [IsProbabilityMeasure (densityMeasure n f)] [IsProbabilityMeasure (densityMeasure n g)]
    (hlcf : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hlcg : LogConcaveDensity (fun x => ENNReal.ofReal (g x)))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (t : ℝ) (ht : 0 < t) :
    let ν := densityMeasure n f
    let η := densityMeasure n g
    let ξ := (ν.prod η).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2)
    let ρ : Measure (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) → ℝ :=
      fun κ => gaussianSmoothingDensity n κ (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    a ^ 2 * (∫ x, matrixHilbertSchmidtSq (densityLogHessian n (ρ ν) x) ∂ouInitialLaw n ν t) +
      b ^ 2 * (∫ x, matrixHilbertSchmidtSq (densityLogHessian n (ρ η) x) ∂ouInitialLaw n η t) -
      (∫ x, matrixHilbertSchmidtSq (densityLogHessian n (ρ ξ) x) ∂ouInitialLaw n ξ t) ≥
      a ^ 2 * b ^ 2 * ∫ p, matrixHilbertSchmidtSq
        (densityLogHessian n (ρ ν) p.1 - densityLogHessian n (ρ η) p.2)
        ∂(ouInitialLaw n ν t).prod (ouInitialLaw n η t) := by
  let E := EuclideanSpace ℝ (Fin n)
  let ν := densityMeasure n f
  let η := densityMeasure n g
  let W : E × E → E := fun p => a • p.1 + b • p.2
  have hW : Measurable W := by dsimp [W]; fun_prop
  let ξ := (ν.prod η).map W
  let : IsProbabilityMeasure ξ := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let c := Real.exp (-t)
  let d := Real.sqrt (1 - Real.exp (-2 * t))
  have hd : 0 < d := (ou_smoothing_scale_domain t ht).2.1
  let ρ : Measure E → E → ℝ := fun κ => gaussianSmoothingDensity n κ c d
  have hν : ouInitialLaw n ν t = densityMeasure n (ρ ν) := gaussianSmoothingDensity_law n ν c d hd
  have hη : ouInitialLaw n η t = densityMeasure n (ρ η) := gaussianSmoothingDensity_law n η c d hd
  have hξ : ouInitialLaw n ξ t = densityMeasure n (ρ ξ) := gaussianSmoothingDensity_law n ξ c d hd
  let : IsProbabilityMeasure (densityMeasure n (ρ ν)) := by rw [← hν]; infer_instance
  let : IsProbabilityMeasure (densityMeasure n (ρ η)) := by rw [← hη]; infer_instance
  have hlc : LogConcaveDensity (fun x => ENNReal.ofReal (ρ ξ x)) :=
    gaussianSmoothing_normalized_convolution_logConcave n f g hf hg hlcf hlcg a b c d hd
  have hlaw := ou_normalized_convolution_density_law n ν η a b hab t ht
  have h := convolution_hessian_hilbertSchmidt_deficit n (ρ ν) (ρ η) (ρ ξ)
    (gaussianSmoothingDensity_smooth n ν c d) (gaussianSmoothingDensity_pos n ν c d hd)
    (gaussianSmoothingDensity_smooth n η c d) (gaussianSmoothingDensity_pos n η c d hd)
    (gaussianSmoothingDensity_smooth n ξ c d) (gaussianSmoothingDensity_pos n ξ c d hd) hlc
    (gaussianSmoothing_ordinaryScore_density_memLp_four n ν c d hd).1
    (gaussianSmoothing_ordinaryScore_density_memLp_four n η c d hd).1
    (fun i j => (gaussianSmoothing_secondDensityRatio_memLp n ν i j c d hd).1)
    (fun i j => (gaussianSmoothing_secondDensityRatio_memLp n η i j c d hd).1) a b ha hb hab hlaw
  dsimp only
  rw [hν, hη, hξ]
  exact h

end AffineFKProof
