module

public import AffineFK.IsotropicCoordinates
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Actual isotropy of a normalized independent convolution

Literal unit raw covariance derives both coordinate L2 domains. Genuine
product integration then proves the image-law means and covariances,
including zero coefficients and dimension zero. The expansion follows
the earlier actual Gaussian-input calculation, with both input means and
covariances now explicit rather than Gaussian-specific facts.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory

theorem normalizedConvolution_isotropy (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (hmeanν : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hmeanη : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂η) = 0)
    (hcovν : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) =
      if i = j then (1 : ℝ) else 0)
    (hcovη : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂η) =
      if i = j then (1 : ℝ) else 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    let ξ := (ν.prod η).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2)
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ξ ∧
      (∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ξ) = 0) ∧
      (∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ξ) =
        if i = j then (1 : ℝ) else 0) := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ := ν.prod η
  let W : E × E → E := fun p => a • p.1 + b • p.2
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hX : MemLp (id : E → E) 2 ν := memLp_piLp_iff.mpr (isotropic_coordinate_memLp n ν hcovν)
  have hY : MemLp (id : E → E) 2 η := memLp_piLp_iff.mpr (isotropic_coordinate_memLp n η hcovη)
  have hWL2 : MemLp W 2 μ := ((hX.comp_fst η).const_smul a).add ((hY.comp_snd ν).const_smul b)
  refine ⟨(memLp_map_measure_iff aestronglyMeasurable_id hW.aemeasurable).mpr hWL2, ?_, ?_⟩
  · intro i
    rw [integral_map hW.aemeasurable
      (show Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) from by fun_prop).aestronglyMeasurable]
    have hx := (hX.eval_piLp i).comp_fst η
    have hy := (hY.eval_piLp i).comp_snd ν
    have heq : (fun p : E × E => (W p) i) = fun p => a * p.1 i + b * p.2 i := by
      funext p
      rfl
    rw [heq, integral_add (f := fun p : E × E => a * p.1 i) (g := fun p => b * p.2 i)
      ((hx.integrable (by norm_num)).const_mul a) ((hy.integrable (by norm_num)).const_mul b),
      integral_const_mul, integral_const_mul]
    have hfst : (∫ p : E × E, p.1 i ∂μ) = 0 := by
      simpa only [hmeanν, probReal_univ, one_smul] using
        integral_fun_fst (μ := ν) (ν := η) (fun x : E => x i)
    have hsnd : (∫ p : E × E, p.2 i ∂μ) = 0 := by
      simpa only [hmeanη, probReal_univ, one_smul] using
        integral_fun_snd (μ := ν) (ν := η) (fun x : E => x i)
    rw [hfst, hsnd, mul_zero, mul_zero, add_zero]
  · intro i j
    rw [integral_map hW.aemeasurable
      (show Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i * x j) from by fun_prop).aestronglyMeasurable]
    have hXi := (hX.eval_piLp i).comp_fst η
    have hXj := (hX.eval_piLp j).comp_fst η
    have hYi := (hY.eval_piLp i).comp_snd ν
    have hYj := (hY.eval_piLp j).comp_snd ν
    have hXX : Integrable (fun p : E × E => p.1 i * p.1 j) μ := hXi.integrable_mul hXj
    have hXY : Integrable (fun p : E × E => p.1 i * p.2 j) μ := hXi.integrable_mul hYj
    have hYX : Integrable (fun p : E × E => p.1 j * p.2 i) μ := hXj.integrable_mul hYi
    have hYY : Integrable (fun p : E × E => p.2 i * p.2 j) μ := hYi.integrable_mul hYj
    have heq : (fun p : E × E => (W p) i * (W p) j) =
        fun p => ((a ^ 2 * (p.1 i * p.1 j) + (a * b) * (p.1 i * p.2 j)) +
          (a * b) * (p.1 j * p.2 i)) + b ^ 2 * (p.2 i * p.2 j) := by
      funext p
      change (a * p.1 i + b * p.2 i) * (a * p.1 j + b * p.2 j) = _
      ring
    rw [heq, integral_add
      (f := fun p : E × E => (a ^ 2 * (p.1 i * p.1 j) + (a * b) * (p.1 i * p.2 j)) +
        (a * b) * (p.1 j * p.2 i)) (g := fun p => b ^ 2 * (p.2 i * p.2 j))
      (((hXX.const_mul _).add (hXY.const_mul _)).add (hYX.const_mul _)) (hYY.const_mul _),
      integral_add (f := fun p : E × E => a ^ 2 * (p.1 i * p.1 j) + (a * b) * (p.1 i * p.2 j))
        (g := fun p => (a * b) * (p.1 j * p.2 i)) ((hXX.const_mul _).add (hXY.const_mul _)) (hYX.const_mul _),
      integral_add (f := fun p : E × E => a ^ 2 * (p.1 i * p.1 j))
        (g := fun p => (a * b) * (p.1 i * p.2 j)) (hXX.const_mul _) (hXY.const_mul _)]
    simp_rw [integral_const_mul]
    have hfst : (∫ p : E × E, p.1 i * p.1 j ∂μ) = if i = j then (1 : ℝ) else 0 := by
      simpa only [hcovν, probReal_univ, one_smul] using
        integral_fun_fst (μ := ν) (ν := η) (fun x : E => x i * x j)
    have hsnd : (∫ p : E × E, p.2 i * p.2 j ∂μ) = if i = j then (1 : ℝ) else 0 := by
      simpa only [hcovη, probReal_univ, one_smul] using
        integral_fun_snd (μ := ν) (ν := η) (fun x : E => x i * x j)
    have hcross (k l : Fin n) : (∫ p : E × E, p.1 k * p.2 l ∂μ) = 0 := by
      rw [integral_prod_mul (μ := ν) (ν := η) (fun x : E => x k) (fun y : E => y l)]
      simp only [hmeanν, zero_mul]
    rw [hfst, hsnd, hcross, hcross]
    calc
      _ = (a ^ 2 + b ^ 2) * (if i = j then (1 : ℝ) else 0) := by ring
      _ = _ := by rw [hab, one_mul]

end AffineFKProof
