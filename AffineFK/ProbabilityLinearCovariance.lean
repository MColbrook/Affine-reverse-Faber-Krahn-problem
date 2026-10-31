module

public import AffineFK.ProbabilityCovarianceMatrix
public import AffineFK.ConditionalMatrixHilbertSchmidt

/-!
# Actual covariance transport by a real matrix

The moment matrix is the genuine Bochner integral of the outer product.
The finite-dimensional conjugation operator commutes with that integral.
All L1 guards follow from actual L2 membership before any image-law
integral is transformed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

def covarianceConjugationLinear (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun C := B * C * Bᴴ
  map_add' C D := by rw [mul_add, add_mul]
  map_smul' c C := by rw [mul_smul_comm, smul_mul_assoc]; rfl

def covarianceConjugationContinuousLinear (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (covarianceConjugationLinear n B).toContinuousLinearMap

theorem covariance_outer_linear_image (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanOuterBilinear n (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B x)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B x) =
      B * euclideanOuterBilinear n x x * Bᴴ := by
  change Matrix.vecMulVec (B *ᵥ (fun i => x i)) (B *ᵥ (fun i => x i)) =
    B * Matrix.vecMulVec (fun i => x i) (fun i => x i) * Bᴴ
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose]
  have hstar (v : Fin n → ℝ) : star v = v := by funext i; exact star_trivial _
  rw [hstar, hstar]

theorem probabilitySecondMomentMatrix_eq_integral_outer (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν) :
    probabilitySecondMomentMatrix n ν = ∫ x, euclideanOuterBilinear n x x ∂ν := by
  have hInt : Integrable (fun x => euclideanOuterBilinear n x x) ν :=
    memLp_one_iff_integrable.mp ((euclideanOuterBilinear n).memLp_of_bilin 1 hX hX)
  ext i j
  have h := (matrixEntryContinuousLinear n i j).integral_comp_comm hInt
  simpa only [probabilitySecondMomentMatrix, matrixEntryContinuousLinear_apply,
    euclideanOuterBilinear_apply] using h

theorem probabilitySecondMomentMatrix_linear_image (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    probabilitySecondMomentMatrix n (ν.map (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B)) =
      B * probabilitySecondMomentMatrix n ν * Bᴴ := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B
  have hT : Measurable T := T.continuous.measurable
  have hTX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (ν.map T) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hT.aemeasurable).mpr (T.comp_memLp' hX)
  have hInt : Integrable (fun x => euclideanOuterBilinear n x x) ν :=
    memLp_one_iff_integrable.mp ((euclideanOuterBilinear n).memLp_of_bilin 1 hX hX)
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => euclideanOuterBilinear n x x) := by fun_prop
  rw [probabilitySecondMomentMatrix_eq_integral_outer n _ hTX,
    integral_map hT.aemeasurable hcont.aestronglyMeasurable]
  calc
    _ = ∫ x, covarianceConjugationContinuousLinear n B (euclideanOuterBilinear n x x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact covariance_outer_linear_image n B x
    _ = covarianceConjugationContinuousLinear n B (∫ x, euclideanOuterBilinear n x x ∂ν) :=
      (covarianceConjugationContinuousLinear n B).integral_comp_comm hInt
    _ = _ := by rw [← probabilitySecondMomentMatrix_eq_integral_outer n ν hX]; rfl

theorem probability_integral_id_zero_of_coordinates (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0) :
    (∫ x : EuclideanSpace ℝ (Fin n), x ∂ν) = 0 := by
  ext i
  have h := (coordinateFunctional n i).integral_comp_comm (hX.integrable (by norm_num))
  simpa only [id_eq, coordinateFunctional_apply, hmean, PiLp.zero_apply] using h.symm

theorem probability_linear_image_mean_zero (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∫ z : EuclideanSpace ℝ (Fin n), z i
      ∂ν.map (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B)) = 0 := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B
  rw [integral_map T.continuous.measurable.aemeasurable
    (show Continuous (fun z : EuclideanSpace ℝ (Fin n) => z i) from by fun_prop).aestronglyMeasurable]
  have h := ((coordinateFunctional n i).comp T).integral_comp_comm (hX.integrable (by norm_num))
  simp only [id_eq] at h
  rw [probability_integral_id_zero_of_coordinates n ν hX hmean, map_zero] at h
  simpa only [id_eq, ContinuousLinearMap.comp_apply, coordinateFunctional_apply] using h

end AffineFKProof
