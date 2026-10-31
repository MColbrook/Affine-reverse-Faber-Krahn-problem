module

public import AffineFK.DirichletLinearRayleigh

/-!
# Linear comparison of the actual variational Dirichlet eigenvalue

Both bounds concern the actual H0 Rayleigh infimum. Positive dimension
ensures a nonzero inverse operator norm, so the ENNReal infimum calculation
also covers empty domains without a zero-times-infinity ambiguity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped ENNReal

theorem dirichletLinearImage_symm (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) :
    dirichletLinearImage n A.symm (dirichletLinearImage n A U) = U := by
  ext x
  change A.symm (A x) ∈ (U : Set (EuclideanSpace ℝ (Fin n))) ↔ x ∈ (U : Set _)
  rw [A.symm_apply_apply]

theorem dirichletEigenvalue_linear_image_le (n : ℕ) (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) :
    dirichletEigenvalue n (dirichletLinearImage n A U) ≤
      ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2) * dirichletEigenvalue n U := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpos : 0 < ‖A.symm.toContinuousLinearMap‖ := A.symm.norm_pos
  have hC : ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hpos)).ne'
  unfold dirichletEigenvalue
  rw [ENNReal.mul_iInf_of_ne hC ENNReal.ofReal_ne_top]
  apply le_iInf
  intro v
  rw [ENNReal.mul_iInf_of_ne hC ENNReal.ofReal_ne_top]
  apply le_iInf
  intro hv
  obtain ⟨w, hw, hR⟩ := dirichlet_linear_rayleigh_transport n A U v hv
  calc
    _ ≤ ENNReal.ofReal (dirichletRayleigh n _ w) := iInf_le_of_le w (iInf_le _ hw)
    _ ≤ ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2 * dirichletRayleigh n U v) :=
      ENNReal.ofReal_le_ofReal hR
    _ = _ := ENNReal.ofReal_mul (sq_nonneg _)

theorem dirichletEigenvalue_linear_pullback_le (n : ℕ) (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) :
    dirichletEigenvalue n U ≤
      ENNReal.ofReal (‖A.toContinuousLinearMap‖ ^ 2) *
        dirichletEigenvalue n (dirichletLinearImage n A U) := by
  have h := dirichletEigenvalue_linear_image_le n hn A.symm (dirichletLinearImage n A U)
  simpa only [dirichletLinearImage_symm, ContinuousLinearEquiv.symm_symm] using h

end AffineFKProof
