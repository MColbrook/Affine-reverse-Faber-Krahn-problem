module

public import AffineFK.SymmetricAffineSpectralReduction
public import AffineFK.Exponents

/-!
# Conditional unrestricted affine reverse Faber--Krahn reduction

The only spectral hypothesis is the explicitly supplied uniform
symmetric unit-volume maximal-Gaussian-position bound. The genuine
large symmetric intersection, interior translation, H0 Rayleigh
monotonicity and exact volume factor prove the unrestricted conclusion
with constant four times the supplied constant. The hypothesis itself,
and in particular a universal Milman existence theorem, are not proved
by this reduction.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Set
open scoped ENNReal Pointwise

set_option maxHeartbeats 800000 in
theorem affine_spectral_bound_from_symmetric_bound (C : ℝ) (hC : 0 < C)
    (hBound : UniformSymmetricGaussianDirichletBound C)
    (n : ℕ) (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty) :
    ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
      dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩ ≠ ∞ ∧
      (dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩).toReal *
        (volume K).toReal ^ ((2 : ℝ) / (n : ℝ)) ≤ 4 * C * (n : ℝ) := by
  obtain ⟨x,c,L,D,_hcc,_hLdef,_hDdef,hLc,hLv,hLi,hLK,_hLsym,
      hDc,hDv,hDi,hDsym,htranslate,hvolume,hlarge⟩ :=
    symmetric_subbody_construction n K hcompact hconvex
      (volume_pos_of_interior_nonempty n K hinterior)
  have hDeven : ∀ y, -y ∈ D ↔ y ∈ D := fun y => (hDsym y).symm
  obtain ⟨S,hDfinite,hDineq⟩ := symmetric_affine_spectral_bound C hC hBound n hn D
    hDc hDv ⟨0,hDi⟩ hDeven
  let A := gaussianPositionSLLinear n S
  have htranslateEig :
      dirichletEigenvalue n ⟨interior (A '' D),isOpen_interior⟩ =
        dirichletEigenvalue n ⟨interior (A '' L),isOpen_interior⟩ := by
    rw [htranslate]
    simpa only [sub_eq_add_neg] using
      dirichletEigenvalue_linear_translated_body n A L (-c)
  have hLfinite : dirichletEigenvalue n ⟨interior (A '' L),isOpen_interior⟩ ≠ ∞ := by
    rw [← htranslateEig]
    exact hDfinite
  have hEigen :
      (dirichletEigenvalue n ⟨interior (A '' K),isOpen_interior⟩).toReal ≤
        (dirichletEigenvalue n ⟨interior (A '' D),isOpen_interior⟩).toReal := by
    rw [htranslateEig]
    exact ENNReal.toReal_mono hLfinite
      (dirichletEigenvalue_linear_body_antitone n A L K hLK)
  have hVL : 0 < (volume L).toReal := affineBody_real_volume_pos n L hLc hLi
  have hVK : 0 < (volume K).toReal := affineBody_real_volume_pos n K hcompact hinterior
  have hLbound :
      (dirichletEigenvalue n ⟨interior (A '' K),isOpen_interior⟩).toReal *
        (volume L).toReal ^ ((2 : ℝ) / (n : ℝ)) ≤ C * (n : ℝ) := by
    calc
      _ ≤ (dirichletEigenvalue n ⟨interior (A '' D),isOpen_interior⟩).toReal *
          (volume L).toReal ^ ((2 : ℝ) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hEigen (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      _ ≤ _ := by simpa only [hvolume] using hDineq
  have hscaled : (volume K).toReal ≤ (2 : ℝ)^n * (volume L).toReal := by
    have h := (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mp hlarge
    simpa only [mul_comm] using h
  have hfour := symmetric_intersection_volume_factor n hn
    (volume K).toReal (volume L).toReal hVK hVL hscaled
  have hproduct : (volume K).toReal ^ ((2 : ℝ) / (n : ℝ)) =
      (volume L).toReal ^ ((2 : ℝ) / (n : ℝ)) *
        ((volume K).toReal / (volume L).toReal) ^ ((2 : ℝ) / (n : ℝ)) := by
    rw [Real.div_rpow hVK.le hVL.le]
    field_simp [(Real.rpow_pos_of_pos hVL ((2 : ℝ) / (n : ℝ))).ne']
  refine ⟨S,dirichletEigenvalue_ne_top n _
    (affineBody_linear_interior_nonempty n A K hinterior),?_⟩
  calc
    _ = ((dirichletEigenvalue n ⟨interior (A '' K),isOpen_interior⟩).toReal *
          (volume L).toReal ^ ((2 : ℝ) / (n : ℝ))) *
        ((volume K).toReal / (volume L).toReal) ^ ((2 : ℝ) / (n : ℝ)) := by
      rw [hproduct]
      ring
    _ ≤ (C * (n : ℝ)) *
        ((volume K).toReal / (volume L).toReal) ^ ((2 : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hLbound (Real.rpow_nonneg (div_nonneg hVK.le hVL.le) _)
    _ ≤ (C * (n : ℝ)) * 4 :=
      mul_le_mul_of_nonneg_left hfour (mul_nonneg hC.le (Nat.cast_nonneg n))
    _ = 4 * C * (n : ℝ) := by ring

theorem affine_reverse_faber_krahn_conditional
    (hSymmetric : ∃ C : ℝ, 0 < C ∧ UniformSymmetricGaussianDirichletBound C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → Convex ℝ K →
      (interior K).Nonempty → ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
        dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩ ≠ ∞ ∧
        (dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩).toReal *
          (volume K).toReal ^ ((2 : ℝ) / (n : ℝ)) ≤ C * (n : ℝ) := by
  obtain ⟨C,hC,hBound⟩ := hSymmetric
  refine ⟨4*C,mul_pos (by norm_num) hC,?_⟩
  intro n hn K hcompact hconvex hinterior
  exact affine_spectral_bound_from_symmetric_bound C hC hBound n hn K hcompact hconvex hinterior

end AffineFKProof
