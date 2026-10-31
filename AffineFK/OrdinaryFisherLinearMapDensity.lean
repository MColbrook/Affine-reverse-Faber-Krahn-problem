module

public import AffineFK.OrdinaryFisherConvolutionDensity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The exact Jacobian density of an invertible linear image

The determinant factor is the absolute determinant of the inverse. The
identity is an equality of actual measures and uses no regularity, moment
or Fisher-information premise. It includes the zero-dimensional space.

The change-of-variables theorem is Mathlib's Haar/Lebesgue determinant
formula, with the imported primary authorship and Apache-2.0 attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

def ordinaryFisherLinearJacobian (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  |LinearMap.det (A.symm : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))|

def ordinaryFisherLinearDensity (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ordinaryFisherLinearJacobian n A * ρ (A.symm z)

theorem ordinaryFisherLinearJacobian_pos (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    0 < ordinaryFisherLinearJacobian n A := by
  exact abs_pos.mpr (LinearEquiv.isUnit_det' A.symm.toLinearEquiv).ne_zero

theorem ordinaryFisherLinearMap_volume (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).map A =
      ENNReal.ofReal (ordinaryFisherLinearJacobian n A) • volume := by
  have hdet : LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≠ 0 :=
    (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  have hd : LinearMap.det (A.symm : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      (LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))⁻¹ :=
    LinearEquiv.det_coe_symm A.toLinearEquiv
  convert Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin n))) hdet using 1
  rw [ordinaryFisherLinearJacobian, hd]

theorem ordinaryFisherLinearDensity_law (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ) :
    (densityMeasure n ρ).map A = densityMeasure n (ordinaryFisherLinearDensity n A ρ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  let K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (ρ (A.symm z)) * f z
  have hK : Measurable K := (hρ.comp A.symm.continuous.measurable).ennreal_ofReal.mul hf
  have hnew : Measurable (fun z => ENNReal.ofReal (ordinaryFisherLinearDensity n A ρ z)) :=
    (measurable_const.mul (hρ.comp A.symm.continuous.measurable)).ennreal_ofReal
  rw [lintegral_map hf A.continuous.measurable, densityMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hρ.ennreal_ofReal
      (g := fun x => f (A x)) (hf.comp A.continuous.measurable)]
  calc
    _ = ∫⁻ x, K (A x) := by
      apply lintegral_congr
      intro x
      simp only [K, A.symm_apply_apply, Pi.mul_apply]
    _ = ∫⁻ z, K z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).map A :=
      (lintegral_map hK A.continuous.measurable).symm
    _ = ENNReal.ofReal (ordinaryFisherLinearJacobian n A) * ∫⁻ z, K z := by
      rw [ordinaryFisherLinearMap_volume, lintegral_smul_measure]
      rfl
    _ = ∫⁻ z, ENNReal.ofReal (ordinaryFisherLinearDensity n A ρ z) * f z := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [ordinaryFisherLinearDensity, ENNReal.ofReal_mul (ordinaryFisherLinearJacobian_pos n A).le]
      exact (mul_assoc _ _ _).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ hnew hf).symm

end AffineFKProof
