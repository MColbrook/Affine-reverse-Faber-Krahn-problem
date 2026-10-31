module

public import AffineFK.GaussianPositionBall
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A literal special-linear normalization of an origin-centred ellipsoid

The inverse ellipsoid map is scaled by the positive nth root of its
absolute determinant. If its orientation is negative, an actual orthogonal
reflection corrects it while preserving the target ball. The construction
uses Mathlib's proved reflection determinant and finite-dimensional Haar
change of variables, not an assumed normalizing position.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal RealInnerProductSpace

theorem gaussianPosition_exists_ball_reflection (n : ℕ) (hn : 0 < n) :
    ∃ J : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      J.toContinuousLinearMap.det = -1 ∧ ∀ x, ‖J x‖ = ‖x‖ := by
  let i : Fin n := ⟨0, hn⟩
  let v := EuclideanSpace.basisFun (Fin n) ℝ i
  have hv : v ≠ 0 := by
    intro hv
    have h : ‖v‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
    rw [hv, norm_zero] at h
    exact zero_ne_one h
  let H := (Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n)))).orthogonal
  refine ⟨H.reflection.toContinuousLinearEquiv, ?_, H.reflection.norm_map⟩
  change LinearMap.det H.reflection.toLinearMap = -1
  rw [H.det_reflection]
  have hH : H.orthogonal = Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin n))) :=
    Submodule.orthogonal_orthogonal _
  rw [hH, finrank_span_singleton hv]
  norm_num

theorem gaussianPosition_ellipsoid_to_volume_one_ball (n : ℕ) (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (R : ℝ) (hR : 0 < R)
    (hvol : volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) = 1) :
    ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ, ∃ r : ℝ,
      0 < r ∧
      gaussianPositionSLLinear n S '' (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) =
        closedBall (0 : EuclideanSpace ℝ (Fin n)) r ∧
      volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) = 1 ∧ r ^ 2 ≤ (n : ℝ) / 4 := by
  let E := EuclideanSpace ℝ (Fin n)
  let d : ℝ := A.toContinuousLinearMap.det
  have hd : d ≠ 0 := (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  let k : ℝ := |d| ^ ((n : ℝ)⁻¹)
  have hk : 0 < k := Real.rpow_pos_of_pos (abs_pos.mpr hd) _
  have hkpow : k ^ n = |d| := Real.rpow_inv_natCast_pow (abs_nonneg d) hn.ne'
  let L0 : E →L[ℝ] E := k • A.symm.toContinuousLinearMap
  have hdet0 : L0.det = |d| * d⁻¹ := by
    change LinearMap.det (k • (A.symm : E →ₗ[ℝ] E)) = _
    rw [LinearMap.det_smul]
    change k ^ Module.finrank ℝ E * A.symm.toContinuousLinearMap.det = _
    rw [ContinuousLinearEquiv.det_coe_symm]
    simp only [E, finrank_euclideanSpace, Fintype.card_fin, hkpow]
    rfl
  obtain ⟨J, hJdet, hJnorm⟩ := gaussianPosition_exists_ball_reflection n hn
  let L : E →L[ℝ] E := if 0 < d then L0 else J.toContinuousLinearMap.comp L0
  have hdet : L.det = 1 := by
    dsimp only [L]
    split_ifs with hpos
    · rw [hdet0, abs_of_pos hpos, mul_inv_cancel₀ hd]
    · have hneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hd
      change LinearMap.det (J.toContinuousLinearMap.toLinearMap.comp L0.toLinearMap) = 1
      rw [LinearMap.det_comp]
      change J.toContinuousLinearMap.det * L0.det = 1
      rw [hJdet, hdet0, abs_of_neg hneg]
      field_simp
  have hnorm0 (u : E) : ‖L0 (A u)‖ = k * ‖u‖ := by
    change ‖k • A.symm (A u)‖ = _
    rw [A.symm_apply_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
  have hnorm (u : E) : ‖L (A u)‖ = k * ‖u‖ := by
    dsimp only [L]
    split_ifs
    · exact hnorm0 u
    · exact (hJnorm (L0 (A u))).trans (hnorm0 u)
  let S := gaussianPositionSLOfOperator n L hdet
  have hS (x : E) : gaussianPositionSLLinear n S x = L x := by
    rw [gaussianPositionSLLinear_apply, gaussianPositionSLOfOperator_apply]
  let r : ℝ := k * R
  have hr : 0 < r := mul_pos hk hR
  have himage : gaussianPositionSLLinear n S '' (A '' closedBall (0 : E) R) =
      closedBall (0 : E) r := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [mem_closedBall, dist_zero_right, hS, hnorm]
      exact mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_zero_right] using hu) hk.le
    · intro x hx
      let y := (gaussianPositionSLLinear n S).symm x
      let u := A.symm y
      have hu : u ∈ closedBall (0 : E) R := by
        rw [mem_closedBall, dist_zero_right]
        have heq : k * ‖u‖ = ‖x‖ := by
          rw [← hnorm, A.apply_symm_apply, ← hS]
          exact congrArg norm ((gaussianPositionSLLinear n S).apply_symm_apply x)
        have hle : k * ‖u‖ ≤ k * R := by
          rw [heq]
          exact (show ‖x‖ ≤ r from by simpa only [mem_closedBall, dist_zero_right] using hx)
        exact (mul_le_mul_iff_right₀ hk).mp hle
      exact ⟨y, ⟨u, hu, A.apply_symm_apply y⟩, (gaussianPositionSLLinear n S).apply_symm_apply x⟩
  have hvolume : volume (closedBall (0 : E) r) = 1 := by
    rw [← himage, Measure.addHaar_image_continuousLinearEquiv, gaussianPositionSLLinear_det]
    simpa only [abs_one, ENNReal.ofReal_one, one_mul] using hvol
  exact ⟨S, r, hr, himage, hvolume, gaussianPosition_volume_one_ball_radius n hn r hr hvolume⟩

end AffineFKProof
