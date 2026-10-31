module

public import AffineFK.GaussianPositionCoordinatePolar
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Exact coordinate/Euclidean Haar-volume transport

Mathlib's volume-preserving PiLp equivalence fixes the normalization,
including dimension zero. No upstream Mahler proof is imported here.
The final arithmetic consequence has its volume-product bound as an
explicit hypothesis and does not assert that bound unconditionally.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped Pointwise ENNReal

theorem gaussianPosition_ofLp_image_volume (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    volume ((WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K) = volume K := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have h := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage_emb
    e.toHomeomorph.measurableEmbedding (e '' K)
  change volume (e ⁻¹' (e '' K)) = volume (e '' K) at h
  rw [Set.preimage_image_eq _ e.injective] at h
  exact h.symm

theorem gaussianPosition_toLp_image_volume (n : ℕ)
    (K : Set (Fin n → ℝ)) :
    volume ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) '' K) = volume K := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have h := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage_emb
    e.toHomeomorph.measurableEmbedding (e '' K)
  change volume (e ⁻¹' (e '' K)) = volume (e '' K) at h
  rw [Set.preimage_image_eq _ e.injective] at h
  exact h.symm

theorem gaussianPosition_coordinatePolar_volume (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hsym : ∀ x ∈ K, -x ∈ K) :
    volume {p : Fin n → ℝ | ∀ v ∈
      (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K,
        (∑ i, p i * v i) ≤ (1 : ℝ)} =
      volume ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  have h := gaussianPosition_toLp_image_volume n
    {p : Fin n → ℝ | ∀ v ∈
      (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K,
        (∑ i, p i * v i) ≤ (1 : ℝ)}
  rw [gaussianPosition_coordinatePolar_image n K hsym] at h
  exact h.symm

theorem gaussianPosition_coordinate_volume_product (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hsym : ∀ x ∈ K, -x ∈ K) :
    (volume ((WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K)).toReal *
      (volume {p : Fin n → ℝ | ∀ v ∈
        (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K,
          (∑ i, p i * v i) ≤ (1 : ℝ)}).toReal =
      volume.real K * volume.real ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  rw [gaussianPosition_ofLp_image_volume, gaussianPosition_coordinatePolar_volume n K hsym]
  rfl

theorem gaussianPosition_factorial_le_dim_pow (n : ℕ) :
    (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
  exact_mod_cast Nat.factorial_le_pow n

theorem gaussianPosition_dilated_polar_lower_of_volume_product (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hvolume : volume K = 1)
    (hLower : (4 : ℝ) ^ n / (Nat.factorial n : ℝ) ≤
      volume.real K * volume.real ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K)) :
    (4 : ℝ) ^ n ≤ volume.real ((n : ℝ) •
      (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  have hFacPos : 0 < (Nat.factorial n : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hM : (4 : ℝ) ^ n / (Nat.factorial n : ℝ) ≤
      volume.real ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
    simpa only [measureReal_def, hvolume, ENNReal.toReal_one, one_mul] using hLower
  calc
    _ ≤ volume.real ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) * (Nat.factorial n : ℝ) :=
      (div_le_iff₀ hFacPos).mp hM
    _ ≤ volume.real ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) * (n : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left (gaussianPosition_factorial_le_dim_pow n)
        (show 0 ≤ volume.real ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) from ENNReal.toReal_nonneg)
    _ = _ := by rw [gaussianPosition_polar_dilation_real_volume]; ring

end AffineFKProof
