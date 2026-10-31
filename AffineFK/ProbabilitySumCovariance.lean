module

public import AffineFK.ConvolutionCovarianceWhitening
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual covariance of an independent sum

This extends the earlier normalized-convolution moment calculation to
the literal unnormalized sum and arbitrary input second-moment matrices.
The proof retains the original product-measure L1 guards and attribution
through NormalizedConvolutionIsotropy and Mathlib's product integrals.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem probability_sum_covariance (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 η)
    (hmeanX : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hmeanY : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂η) = 0) :
    let κ := (ν.prod η).map (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 + p.2)
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 κ ∧
      (∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂κ) = 0) ∧
      probabilitySecondMomentMatrix n κ = probabilitySecondMomentMatrix n ν + probabilitySecondMomentMatrix n η := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ := ν.prod η
  let W : E × E → E := fun p => p.1 + p.2
  have hW : Measurable W := by dsimp only [W]; fun_prop
  have hWL2 : MemLp W 2 μ := (hX.comp_fst η).add (hY.comp_snd ν)
  refine ⟨(memLp_map_measure_iff aestronglyMeasurable_id hW.aemeasurable).mpr hWL2, ?_, ?_⟩
  · intro i
    rw [integral_map hW.aemeasurable
      (show Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) from by fun_prop).aestronglyMeasurable]
    have hXi : Integrable (fun p : E × E => p.1 i) μ := by
      simpa only [id_eq] using ((hX.eval_piLp i).comp_fst η).integrable (by norm_num)
    have hYi : Integrable (fun p : E × E => p.2 i) μ := by
      simpa only [id_eq] using ((hY.eval_piLp i).comp_snd ν).integrable (by norm_num)
    change (∫ p : E × E, p.1 i + p.2 i ∂μ) = 0
    rw [integral_add hXi hYi]
    have hfst : (∫ p : E × E, p.1 i ∂μ) = 0 := by
      simpa only [hmeanX, probReal_univ, one_smul] using integral_fun_fst (μ := ν) (ν := η) (fun x : E => x i)
    have hsnd : (∫ p : E × E, p.2 i ∂μ) = 0 := by
      simpa only [hmeanY, probReal_univ, one_smul] using integral_fun_snd (μ := ν) (ν := η) (fun x : E => x i)
    rw [hfst, hsnd, add_zero]
  · ext i j
    change (∫ x : E, x i * x j ∂μ.map W) =
      (∫ x : E, x i * x j ∂ν) + (∫ x : E, x i * x j ∂η)
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
    have heq : (fun p : E × E => (W p) i * (W p) j) = fun p =>
        ((p.1 i * p.1 j + p.1 i * p.2 j) + p.1 j * p.2 i) + p.2 i * p.2 j := by
      funext p
      change (p.1 i + p.2 i) * (p.1 j + p.2 j) = _
      ring
    rw [heq,
      integral_add
        (f := fun p : E × E => (p.1 i * p.1 j + p.1 i * p.2 j) + p.1 j * p.2 i)
        (g := fun p : E × E => p.2 i * p.2 j) ((hXX.add hXY).add hYX) hYY,
      integral_add
        (f := fun p : E × E => p.1 i * p.1 j + p.1 i * p.2 j)
        (g := fun p : E × E => p.1 j * p.2 i) (hXX.add hXY) hYX,
      integral_add (f := fun p : E × E => p.1 i * p.1 j)
        (g := fun p : E × E => p.1 i * p.2 j) hXX hXY]
    have hfst : (∫ p : E × E, p.1 i * p.1 j ∂μ) = ∫ x : E, x i * x j ∂ν := by
      simpa only [probReal_univ, one_smul] using integral_fun_fst (μ := ν) (ν := η) (fun x : E => x i * x j)
    have hsnd : (∫ p : E × E, p.2 i * p.2 j ∂μ) = ∫ x : E, x i * x j ∂η := by
      simpa only [probReal_univ, one_smul] using integral_fun_snd (μ := ν) (ν := η) (fun x : E => x i * x j)
    have hcross (k l : Fin n) : (∫ p : E × E, p.1 k * p.2 l ∂μ) = 0 := by
      rw [integral_prod_mul (μ := ν) (ν := η) (fun x : E => x k) (fun y : E => y l)]
      simp only [hmeanX, zero_mul]
    rw [hfst, hsnd, hcross, hcross, add_zero, add_zero]

theorem probability_sum_covariance_scalar_left (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 η)
    (hmeanX : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hmeanY : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂η) = 0)
    (α : ℝ) (hcovX : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) =
      if i = j then α else 0) :
    let κ := (ν.prod η).map (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 + p.2)
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 κ ∧
      (∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂κ) = 0) ∧
      probabilitySecondMomentMatrix n κ = convolutionCovarianceMatrix n α η := by
  have h := probability_sum_covariance n ν η hX hY hmeanX hmeanY
  have hC : probabilitySecondMomentMatrix n ν = α • 1 := by
    ext i j
    simp only [probabilitySecondMomentMatrix, hcovX, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  exact ⟨h.1, h.2.1, by rw [h.2.2, hC]; rfl⟩

end AffineFKProof
