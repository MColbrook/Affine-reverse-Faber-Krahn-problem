module

public import AffineFK.OpenAIMahler.Analysis.Mahler.MainTheorem
public import AffineFK.GaussianPositionPolarVolumeTransport
public import AffineFK.GaussianPositionTiltJacobian
public import AffineFK.CovarianceEllipsoidTiltConstruction
public import AffineFK.GaussianEllipsoidSpectralReduction

/-!
# The volume-one intersection ellipsoid and the affine spectral conclusion

The genuine pinned symmetric Mahler proof supplies a stronger volume
product than the reverse-volume-product input needed here. Exact Haar
and polar transport give volume(n K^polar)>=4^n. The actual log-Laplace
area bound selects a genuine small-determinant tilt. Its derived covariance
ellipsoid, central intersection maximum and volume normalization give
the literal volume-one origin ellipsoid with one universal positive base.
The previously proved analytic and affine reductions then apply.

Proof reuse: OpenAI math development, commit
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, original Apache-2.0 sources and
attribution retained in OpenAIMahler/ and the port provenance manifests.
All subsequent volume, covariance, Gaussian and H0 quantities below are
the actual quantities of the original manuscript, with no output premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Set Metric
open scoped ENNReal Pointwise

theorem gaussianPosition_mahler_volume_product (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) (heven : ∀ x, -x ∈ K ↔ x ∈ K) :
    (4 : ℝ)^n / (Nat.factorial n : ℝ) ≤
      volume.real K * volume.real ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  have hneg : ∀ x ∈ K, -x ∈ K := fun x hx => (heven x).mpr hx
  obtain ⟨hKc,hconvc,hevenc,hinteriorc⟩ :=
    gaussianPosition_coordinate_body n K hK hconv hneg hinterior
  have h := OAI.SymmetricMahler.symmetric_mahler (show 1 ≤ n from hn)
    hKc hconvc hevenc hinteriorc
  rw [← gaussianPosition_coordinate_volume_product n K hneg]
  exact h

theorem gaussianPosition_dilated_polar_uniform_volume_lower (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) (heven : ∀ x, -x ∈ K ↔ x ∈ K)
    (hvolume : volume K = 1) :
    (4 : ℝ)^n ≤ volume.real ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) :=
  gaussianPosition_dilated_polar_lower_of_volume_product n K hvolume
    (gaussianPosition_mahler_volume_product n hn K hK hconv hinterior heven)

set_option maxHeartbeats 1000000 in
theorem gaussianPosition_uniform_volume_one_ellipsoid_intersection :
    ∃ a : ℝ, 0 < a ∧ UniformVolumeOneEllipsoidIntersection a := by
  refine ⟨covarianceEllipsoidTiltIntersectionBase 4, covarianceEllipsoidTiltIntersectionBase_pos 4, ?_⟩
  intro n hn K hK hconv hinterior heven hvolume
  let U := (n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K
  obtain ⟨_hUc,hUm,_hUconv,_hUzero,_hUpos,hUfinite,_hUreal⟩ :=
    gaussianPosition_dilated_polar_finite_volume n hn K hK hconv hinterior heven
  have hUlower : (4 : ℝ)^n ≤ volume.real U :=
    gaussianPosition_dilated_polar_uniform_volume_lower n hn K hK hconv hinterior heven hvolume
  obtain ⟨y,hy,hAbsDet⟩ := gaussianPositionLogLaplace_exists_small_jacobian_of_volume_lower
    n K hK hconv hvolume U hUm hUfinite 4 (by norm_num) hUlower
  have hdet : LinearMap.det ((fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≤ ((4 : ℝ)⁻¹)^n :=
    (le_abs_self _).trans hAbsDet
  obtain ⟨A,hVol,hIntersection⟩ := exists_tilt_volume_one_origin_ellipsoid
    n hn K hK hconv hinterior hvolume heven y hy 4 (by norm_num) hdet
  exact ⟨A,Real.sqrt (2*(n : ℝ)),
    Real.sqrt_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr hn)),hVol,hIntersection⟩

theorem affine_reverse_faber_krahn :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → Convex ℝ K →
      (interior K).Nonempty → ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
        dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩ ≠ ∞ ∧
        (dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩).toReal *
          (volume K).toReal ^ ((2 : ℝ) / (n : ℝ)) ≤ C * (n : ℝ) :=
  affine_reverse_faber_krahn_of_ellipsoid_intersections
    gaussianPosition_uniform_volume_one_ellipsoid_intersection

end AffineFKProof
