module

public import AffineFK.GaussianKernelDerivativeBounds
public import AffineFK.OrdinaryFisherLinearMapDensity
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The literal special-linear action on Euclidean Gaussian measure

The determinant-one matrix is transported through the standard Euclidean
basis. Its induced continuous linear equivalence preserves actual
Lebesgue volume. Change of variables therefore identifies the Gaussian
measure of its image with the fixed-domain Gaussian integral.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

theorem gaussianPosition_matrix_det (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)) = A.det := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

def gaussianPositionSLLinear (n : ℕ) (S : Matrix.SpecialLinearGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (S : Matrix (Fin n) (Fin n) ℝ)).toLinearMap.equivOfDetNeZero
    (by rw [gaussianPosition_matrix_det, S.det_coe]; exact one_ne_zero)).toContinuousLinearEquiv

theorem gaussianPositionSLLinear_apply (n : ℕ) (S : Matrix.SpecialLinearGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianPositionSLLinear n S x = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (S : Matrix (Fin n) (Fin n) ℝ) x := rfl

theorem gaussianPositionSLLinear_det (n : ℕ) (S : Matrix.SpecialLinearGroup (Fin n) ℝ) :
    LinearMap.det (gaussianPositionSLLinear n S : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)) = 1 := by
  change LinearMap.det (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = 1
  rw [gaussianPosition_matrix_det, S.det_coe]

theorem gaussianPositionSLLinear_preserves_volume (n : ℕ)
    (S : Matrix.SpecialLinearGroup (Fin n) ℝ) :
    MeasurePreserving (gaussianPositionSLLinear n S) volume volume := by
  refine ⟨(gaussianPositionSLLinear n S).continuous.measurable, ?_⟩
  rw [ordinaryFisherLinearMap_volume]
  have hJ : ordinaryFisherLinearJacobian n (gaussianPositionSLLinear n S) = 1 := by
    rw [ordinaryFisherLinearJacobian]
    change |LinearMap.det ((gaussianPositionSLLinear n S).toLinearEquiv.symm :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| = 1
    rw [LinearEquiv.det_coe_symm, gaussianPositionSLLinear_det]
    norm_num
  simp only [hJ, ENNReal.ofReal_one, one_smul]

theorem gaussianPosition_gaussian_measure_integral (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (S : Matrix.SpecialLinearGroup (Fin n) ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real (gaussianPositionSLLinear n S '' K) =
      ∫ x in K, standardGaussianDensity n (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (S : Matrix (Fin n) (Fin n) ℝ) x) := by
  let A := gaussianPositionSLLinear n S
  have hAK : IsCompact (A '' K) := hK.image A.continuous
  have hInt : IntegrableOn (standardGaussianDensity n) (A '' K) :=
    ContinuousOn.integrableOn_compact hAK (standardGaussianDensity_smooth n).continuous.continuousOn
  have hmass : (stdGaussian (EuclideanSpace ℝ (Fin n))) (A '' K) =
      ENNReal.ofReal (∫ x in A '' K, standardGaussianDensity n x) := by
    rw [stdGaussian_eq_densityMeasure, densityMeasure, withDensity_apply _ hAK.measurableSet,
      ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall fun x => (standardGaussianDensity_pos n x).le)]
  change ((stdGaussian (EuclideanSpace ℝ (Fin n))) (A '' K)).toReal = _
  rw [hmass, ENNReal.toReal_ofReal (integral_nonneg fun x => (standardGaussianDensity_pos n x).le)]
  exact (gaussianPositionSLLinear_preserves_volume n S).setIntegral_image_emb
    A.toHomeomorph.measurableEmbedding (standardGaussianDensity n) K

theorem gaussianPosition_gaussian_set_integral (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x in K, f x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫ x in K, f x * standardGaussianDensity n x := by
  calc
    _ = ∫ x, K.indicator f x ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      (integral_indicator hK).symm
    _ = ∫ x, standardGaussianDensity n x * K.indicator f x := by
      rw [stdGaussian_eq_densityMeasure, density_integral_eq n (standardGaussianDensity n)
        (standardGaussianDensity_smooth n).continuous (fun x => (standardGaussianDensity_pos n x).le)]
    _ = ∫ x, K.indicator (fun y => f y * standardGaussianDensity n y) x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ K
        · simp only [Set.indicator_of_mem hx]
          ring
        · simp only [Set.indicator_of_notMem hx]
          ring
    _ = _ := integral_indicator hK

end AffineFKProof
