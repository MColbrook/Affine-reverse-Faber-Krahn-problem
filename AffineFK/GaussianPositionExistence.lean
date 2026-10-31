module

public import AffineFK.GaussianPositionStationarity
public import AffineFK.GaussianPositionCoercivity
public import Mathlib.Topology.Order.Compact

/-!
# Existence of an actual maximal Gaussian position

Positive superlevel sets of the genuine fixed-domain Gaussian integral
are bounded. Closedness of the determinant-one constraint gives compact
superlevel sets, and the extreme-value theorem supplies a maximizer.
The resulting matrix is literally special-linear. Milman's ellipsoid
theorem is not used for existence.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem gaussianPositionIntegral_identity_pos (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K) :
    0 < gaussianPositionIntegral n K (ContinuousLinearMap.id ℝ _) := by
  have hInt : IntegrableOn (standardGaussianDensity n) K :=
    ContinuousOn.integrableOn_compact hK (standardGaussianDensity_smooth n).continuous.continuousOn
  have hsupp : Function.support (standardGaussianDensity n) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (standardGaussianDensity_pos n x).ne'
  change 0 < ∫ x in K, standardGaussianDensity n x
  apply (integral_pos_iff_support_of_nonneg (fun x => (standardGaussianDensity_pos n x).le) hInt).mpr
  simpa only [hsupp, Measure.restrict_apply_univ] using hvol

theorem gaussianPositionIntegral_maximizer (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K) :
    ∃ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = 1 ∧
      ∀ B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        LinearMap.det (B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = 1 →
        gaussianPositionIntegral n K B ≤ gaussianPositionIntegral n K A := by
  let H := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
  let F : H → ℝ := gaussianPositionIntegral n K
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun A =>
    (gaussianPositionIntegral_hasFDerivAt n K hK A).continuousAt
  have hdet : Continuous (fun A : H => A.det) :=
    ContinuousLinearMap.continuous_det (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
  have hpos := gaussianPositionIntegral_identity_pos n K hK hvol
  let c := F (ContinuousLinearMap.id ℝ _) / 2
  have hc : 0 < c := half_pos hpos
  let S : Set H := {A | A.det = 1 ∧ c ≤ F A}
  have hclosed : IsClosed S :=
    (isClosed_eq hdet continuous_const).inter (isClosed_le continuous_const hF)
  have hbdd : Bornology.IsBounded S :=
    (gaussianPosition_positive_superlevel_bounded n K hK c hc).subset (fun _ h => h.2)
  have hcompact : IsCompact S := by
    rw [← hclosed.closure_eq]
    exact hbdd.isCompact_closure
  have hid : (ContinuousLinearMap.id ℝ _) ∈ S := by
    refine ⟨?_, ?_⟩
    · change LinearMap.det (LinearMap.id : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin n)) = 1
      exact LinearMap.det_id
    · change F (ContinuousLinearMap.id ℝ _) / 2 ≤ F (ContinuousLinearMap.id ℝ _)
      linarith
  obtain ⟨A, hA, hmax⟩ := hcompact.exists_isMaxOn ⟨_, hid⟩ hF.continuousOn
  refine ⟨A, hA.1, ?_⟩
  intro B hB
  by_cases hcB : c ≤ F B
  · exact hmax ⟨hB, hcB⟩
  · exact (lt_of_not_ge hcB).le.trans hA.2

def gaussianPositionSLOfOperator (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)) = 1) : Matrix.SpecialLinearGroup (Fin n) ℝ :=
  ⟨(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm A, by
    rw [← gaussianPosition_matrix_det,
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply]
    exact hA⟩

theorem gaussianPositionSLOfOperator_apply (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)) = 1) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (gaussianPositionSLOfOperator n A hA : Matrix (Fin n) (Fin n) ℝ) = A :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply A

theorem gaussianPositionSLLinear_mul (n : ℕ)
    (S T : Matrix.SpecialLinearGroup (Fin n) ℝ) :
    (fun x => gaussianPositionSLLinear n (T * S) x) =
      (fun x => gaussianPositionSLLinear n T (gaussianPositionSLLinear n S x)) := by
  funext x
  simp only [gaussianPositionSLLinear_apply, Matrix.SpecialLinearGroup.coe_mul, map_mul]
  rfl

theorem gaussianPosition_exists_maximal (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K) :
    ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
      GaussianPositionMaximal n (gaussianPositionSLLinear n S '' K) := by
  obtain ⟨A, hA, hmax⟩ := gaussianPositionIntegral_maximizer n K hK hvol
  let S := gaussianPositionSLOfOperator n A hA
  have hSA : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (S : Matrix (Fin n) (Fin n) ℝ) = A := gaussianPositionSLOfOperator_apply n A hA
  refine ⟨S, ?_⟩
  intro T
  have hTS : gaussianPositionSLLinear n T '' (gaussianPositionSLLinear n S '' K) =
      gaussianPositionSLLinear n (T * S) '' K := by
    rw [image_image]
    congr 1
    exact (gaussianPositionSLLinear_mul n S T).symm
  rw [hTS]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (stdGaussian (EuclideanSpace ℝ (Fin n))).real (gaussianPositionSLLinear n (T * S) '' K) ≤
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real (gaussianPositionSLLinear n S '' K)
  rw [gaussianPosition_gaussian_measure_integral n K hK (T * S),
    gaussianPosition_gaussian_measure_integral n K hK S]
  change gaussianPositionIntegral n K
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (T * S : Matrix (Fin n) (Fin n) ℝ)) ≤
    gaussianPositionIntegral n K (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (S : Matrix (Fin n) (Fin n) ℝ))
  rw [hSA]
  apply hmax
  exact (gaussianPosition_matrix_det n (T * S : Matrix (Fin n) (Fin n) ℝ)).trans (T * S).det_coe

end AffineFKProof
