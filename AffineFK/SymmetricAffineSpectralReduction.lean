module

public import AffineFK.DirichletAffineBodyTransport
public import AffineFK.AffineBodyVolumeNormalization
public import AffineFK.GaussianPositionExistence
public import AffineFK.DirichletRayleighFinite

/-!
# Symmetric affine reduction from an explicitly supplied spectral bound

The hypothesis is the literal unit-volume maximal-Gaussian-position
spectral estimate. Actual special-linear maximal position exists by the
previous proved construction. The spectral estimate itself remains an
explicit hypothesis; no universal Milman theorem is claimed here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal Pointwise

def UniformSymmetricGaussianDirichletBound (C : ℝ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)),
    IsCompact K → Convex ℝ K → (interior K).Nonempty →
    (∀ x, -x ∈ K ↔ x ∈ K) → volume K = 1 → GaussianPositionMaximal n K →
    dirichletEigenvalue n ⟨interior K,isOpen_interior⟩ ≤ ENNReal.ofReal (C * (n : ℝ))

set_option maxHeartbeats 800000 in
theorem symmetric_affine_spectral_bound (C : ℝ) (hC : 0 < C)
    (hBound : UniformSymmetricGaussianDirichletBound C)
    (n : ℕ) (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty) (heven : ∀ x, -x ∈ K ↔ x ∈ K) :
    ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
      dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩ ≠ ∞ ∧
      (dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩).toReal *
        (volume K).toReal ^ ((2 : ℝ) / (n : ℝ)) ≤ C * (n : ℝ) := by
  obtain ⟨r,hr,_hrformula,hrvolume,hrfactor⟩ := affineBody_volume_normalization n hn K
    hcompact.measure_ne_top (volume_pos_of_interior_nonempty n K hinterior)
  have hcompact0 : IsCompact (r • K) := IsCompact.smul r hcompact
  have hconvex0 : Convex ℝ (r • K) := hconvex.smul r
  have hinterior0 : (interior (r • K)).Nonempty := by
    rw [interior_smul₀ hr.ne']
    obtain ⟨x,hx⟩ := hinterior
    exact ⟨r • x,⟨x,hx,rfl⟩⟩
  have heven0 : ∀ x, -x ∈ r • K ↔ x ∈ r • K :=
    affineBody_linear_even n (supportDilationLinearEquiv n r hr.ne') K heven
  obtain ⟨S,hmax⟩ := gaussianPosition_exists_maximal n (r • K) hcompact0
    (by rw [hrvolume]; exact zero_lt_one)
  let A := gaussianPositionSLLinear n S
  have hAcompact : IsCompact (A '' (r • K)) := hcompact0.image A.continuous
  have hAconvex : Convex ℝ (A '' (r • K)) := hconvex0.linear_image A.toLinearMap
  have hAinterior : (interior (A '' (r • K))).Nonempty :=
    affineBody_linear_interior_nonempty n A (r • K) hinterior0
  have hAeven : ∀ x, -x ∈ A '' (r • K) ↔ x ∈ A '' (r • K) :=
    affineBody_linear_even n A (r • K) heven0
  have hAvolume : volume (A '' (r • K)) = 1 := by
    rw [affineBody_SL_volume,hrvolume]
  have hB := hBound n hn (A '' (r • K)) hAcompact hAconvex hAinterior hAeven hAvolume hmax
  have hscale :
      dirichletEigenvalue n ⟨interior (A '' (r • K)),isOpen_interior⟩ =
        ENNReal.ofReal ((volume K).toReal ^ ((2 : ℝ) / (n : ℝ))) *
          dirichletEigenvalue n ⟨interior (A '' K),isOpen_interior⟩ := by
    rw [affineBody_linear_smul_image]
    simpa only [hrfactor] using dirichletEigenvalue_interior_scalar n hn (A '' K) r hr
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hB
  rw [hscale,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg ENNReal.toReal_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg hC.le (Nat.cast_nonneg n))] at hreal
  refine ⟨S,dirichletEigenvalue_ne_top n _
    (affineBody_linear_interior_nonempty n A K hinterior),?_⟩
  simpa only [mul_comm] using hreal

end AffineFKProof
