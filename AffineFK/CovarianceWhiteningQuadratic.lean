module

public import Mathlib.Analysis.Matrix.Order

/-! Real Euclidean quadratic-form bounds for the genuine covariance square root. -/

@[expose] public noncomputable section
namespace AffineFKProof
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

theorem covariance_matrix_quadratic_lower (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hlower : (M - α • 1).PosSemidef)
    (x : EuclideanSpace ℝ (Fin n)) :
    α * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M x⟫ := by
  have h := hlower.dotProduct_mulVec_nonneg (fun i => x i)
  have h' : 0 ≤ ⟪x, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M - α • 1) x⟫ := by
    simpa only [Matrix.inner_toEuclideanCLM, star_trivial] using h
  have heq : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (M - α • 1) x =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M x - α • x := by
    rw [map_sub, map_smul, map_one]
    rfl
  rw [heq, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h'
  linarith

theorem covariance_matrix_quadratic_upper (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (β : ℝ) (hupper : (β • 1 - M).PosSemidef)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M x⟫ ≤ β * ‖x‖ ^ 2 := by
  have h := hupper.dotProduct_mulVec_nonneg (fun i => x i)
  have h' : 0 ≤ ⟪x, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (β • 1 - M) x⟫ := by
    simpa only [Matrix.inner_toEuclideanCLM, star_trivial] using h
  have heq : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (β • 1 - M) x =
      β • x - Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M x := by
    rw [map_sub, map_smul, map_one]
    rfl
  rw [heq, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h'
  linarith

theorem covariance_sqrt_apply_norm_sq (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (CFC.sqrt M) x‖ ^ 2 =
      ⟪x, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M x⟫ := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
  have hS : (CFC.sqrt M).PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  have hprod : (T (CFC.sqrt M)).adjoint.comp (T (CFC.sqrt M)) = T M := by
    change star (T (CFC.sqrt M)) * T (CFC.sqrt M) = T M
    rw [← map_star, ← map_mul]
    congr 1
    rw [show star (CFC.sqrt M) = CFC.sqrt M from hS.isHermitian,
      CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg]
  have h := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left (T (CFC.sqrt M)) x
  rw [hprod] at h
  simpa only [RCLike.re_to_real, real_inner_comm] using h

end AffineFKProof
