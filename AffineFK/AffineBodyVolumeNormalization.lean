module

public import AffineFK.IntersectionVolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual unit-volume normalization for the affine reduction

The genuine Haar scaling formula gives volume one, and real-power
calculus gives the precise inverse-square eigenvalue factor. No
spectral conclusion is assumed in these geometric identities.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped ENNReal Pointwise

theorem affineBody_real_volume_pos (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact K)
    (hinterior : (interior K).Nonempty) : 0 < (volume K).toReal :=
  ENNReal.toReal_pos (volume_pos_of_interior_nonempty n K hinterior).ne'
    hcompact.measure_ne_top

theorem affineBody_volume_normalization (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hfinite : volume K ≠ ∞) (hpos : 0 < volume K) :
    ∃ r : ℝ, 0 < r ∧ r = (volume K).toReal ^ (-1 / (n : ℝ)) ∧
      volume (r • K) = 1 ∧
      (r^2)⁻¹ = (volume K).toReal ^ ((2 : ℝ) / (n : ℝ)) := by
  let V := (volume K).toReal
  have hV : 0 < V := ENNReal.toReal_pos hpos.ne' hfinite
  let s := V ^ ((n : ℝ)⁻¹)
  have hs : 0 < s := Real.rpow_pos_of_pos hV _
  have hsn : s^n = V := Real.rpow_inv_natCast_pow hV.le hn.ne'
  let r := s⁻¹
  have hr : 0 < r := inv_pos.mpr hs
  have hrn : r^n = V⁻¹ := by dsimp only [r]; rw [inv_pow,hsn]
  have hformula : r = V ^ (-1 / (n : ℝ)) := by
    change (V ^ ((n : ℝ)⁻¹))⁻¹ = V ^ (-1 / (n : ℝ))
    rw [← Real.rpow_neg hV.le]
    congr 1
    simp only [neg_div,one_div]
  have hvolume : volume (r • K) = 1 := by
    rw [Measure.addHaar_smul_of_nonneg volume hr.le,
      finrank_euclideanSpace,Fintype.card_fin,hrn,ENNReal.ofReal_inv_of_pos hV]
    dsimp only [V]
    rw [ENNReal.ofReal_toReal hfinite,ENNReal.inv_mul_cancel hpos.ne' hfinite]
  have hfactor : (r^2)⁻¹ = V ^ ((2 : ℝ) / (n : ℝ)) := by
    change (((V ^ ((n : ℝ)⁻¹))⁻¹)^2)⁻¹ = V ^ ((2 : ℝ) / (n : ℝ))
    rw [inv_pow,inv_inv,← Real.rpow_mul_natCast hV.le]
    congr 1
    simp only [Nat.cast_ofNat,div_eq_mul_inv,mul_comm]
  exact ⟨r,hr,hformula,hvolume,hfactor⟩

end AffineFKProof
