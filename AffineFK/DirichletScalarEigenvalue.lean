module

public import AffineFK.DirichletLinearEigenvalue
public import AffineFK.DirichletSupportL2Dilation

/-!
# Exact positive scalar dilation of the actual Dirichlet eigenvalue

Both inequalities come from the proved transport of the genuine H0
Rayleigh infimum. The positive finite coefficients cancel in ENNReal,
so empty domains and infinite eigenvalues are included. Positive natural
dimension is the standing dimension assumption in the paper.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped ENNReal Pointwise

def dirichletScalarImage (n : ℕ) (r : ℝ) (hr : 0 < r)
    (U : Opens (EuclideanSpace ℝ (Fin n))) : Opens (EuclideanSpace ℝ (Fin n)) :=
  dirichletLinearImage n (supportDilationLinearEquiv n r hr.ne') U

theorem dirichletScalarImage_coe (n : ℕ) (r : ℝ) (hr : 0 < r)
    (U : Opens (EuclideanSpace ℝ (Fin n))) :
    (dirichletScalarImage n r hr U : Set (EuclideanSpace ℝ (Fin n))) = r • (U : Set _) := by
  rw [dirichletScalarImage,dirichletLinearImage_coe]
  rfl

theorem supportDilation_norm_le (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ‖(supportDilationLinearEquiv n r hr.ne').toContinuousLinearMap‖ ≤ r := by
  change ‖r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ r
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))) hr.le

theorem supportDilation_inverse_norm_le (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ‖(supportDilationLinearEquiv n r hr.ne').symm.toContinuousLinearMap‖ ≤ r⁻¹ := by
  change ‖r⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ r⁻¹
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))) (inv_nonneg.mpr hr.le)

theorem dirichletEigenvalue_scalar_image (n : ℕ) (hn : 0 < n)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (r : ℝ) (hr : 0 < r) :
    dirichletEigenvalue n (dirichletScalarImage n r hr U) =
      ENNReal.ofReal ((r^2)⁻¹) * dirichletEigenvalue n U := by
  let A := supportDilationLinearEquiv n r hr.ne'
  have hAsq : ‖A.toContinuousLinearMap‖^2 ≤ r^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (supportDilation_norm_le n r hr) 2
  have hAisq : ‖A.symm.toContinuousLinearMap‖^2 ≤ (r⁻¹)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (supportDilation_inverse_norm_le n r hr) 2
  have hforward : dirichletEigenvalue n (dirichletScalarImage n r hr U) ≤
      ENNReal.ofReal ((r⁻¹)^2) * dirichletEigenvalue n U :=
    (dirichletEigenvalue_linear_image_le n hn A U).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hAisq) le_rfl)
  have hreverse : dirichletEigenvalue n U ≤
      ENNReal.ofReal (r^2) * dirichletEigenvalue n (dirichletScalarImage n r hr U) :=
    (dirichletEigenvalue_linear_pullback_le n hn A U).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hAsq) le_rfl)
  have hcancel : ENNReal.ofReal ((r⁻¹)^2) * ENNReal.ofReal (r^2) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    have he : (r⁻¹)^2*r^2 = 1 := by field_simp
    rw [he,ENNReal.ofReal_one]
  have hback : ENNReal.ofReal ((r⁻¹)^2) * dirichletEigenvalue n U ≤
      dirichletEigenvalue n (dirichletScalarImage n r hr U) := by
    calc
      _ ≤ ENNReal.ofReal ((r⁻¹)^2) * (ENNReal.ofReal (r^2) *
          dirichletEigenvalue n (dirichletScalarImage n r hr U)) :=
        mul_le_mul' le_rfl hreverse
      _ = _ := by rw [← mul_assoc,hcancel,one_mul]
  simpa only [inv_pow] using le_antisymm hforward hback

end AffineFKProof
