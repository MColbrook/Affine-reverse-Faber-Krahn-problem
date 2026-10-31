module

public import AffineFK.GaussianPositionEllipsoidMap
public import AffineFK.SymmetricConvexInterior
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Normalizing a supplied approximate M-ellipsoid to volume one

The actual Haar scaling formula and convexity prove that an ellipsoid
with volume at most B^n and central intersection at least a^n can be
rescaled to volume one, retaining intersection at least
(a/max(B,1))^n. This is an implication from supplied actual ellipsoid
data; universal existence of approximate M-ellipsoids is not proved.

The geometric input agrees with the usual approximate M-ellipsoid
conditions, for example Klartag's ETH 2025 Lecture 7, Definition 7.3.
Mathlib's actual Haar scaling is due to Floris van Doorn, Sebastien
Gouezel and contributors, under its retained Apache-2.0 attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Metric
open scoped ENNReal Pointwise

theorem gaussianPosition_shrink_intersection_volume (n : ℕ)
    (K L : Set (EuclideanSpace ℝ (Fin n))) (hK : Convex ℝ K)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    (t : ℝ) (ht : 0 ≤ t) (htOne : t ≤ 1) :
    ENNReal.ofReal (t ^ n) * volume (K ∩ L) ≤ volume (K ∩ t • L) := by
  have hsub : t • (K ∩ L) ⊆ K ∩ t • L := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hK.smul_mem_of_zero_mem hzero hx.1 ⟨ht, htOne⟩, ⟨x, hx.2, rfl⟩⟩
  have h : volume (t • (K ∩ L)) ≤ volume (K ∩ t • L) := measure_mono hsub
  rw [Measure.addHaar_smul_of_nonneg volume ht,
    finrank_euclideanSpace, Fintype.card_fin] at h
  exact h

theorem gaussianPosition_enlarge_convex_set (n : ℕ)
    (L : Set (EuclideanSpace ℝ (Fin n))) (hL : Convex ℝ L)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ L)
    (t : ℝ) (ht : 0 < t) (htOne : 1 ≤ t) : L ⊆ t • L := by
  intro x hx
  have hinv : t⁻¹ ≤ (1 : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_one ht).mpr htOne
  refine ⟨t⁻¹ • x, hL.smul_mem_of_zero_mem hzero hx ⟨inv_nonneg.mpr ht.le, hinv⟩, ?_⟩
  change t • (t⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

theorem gaussianPosition_normalize_convex_intersection (n : ℕ) (hn : 0 < n)
    (K L : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (hKzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K)
    (hL : IsCompact L) (hLconv : Convex ℝ L)
    (hLzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ L)
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hvolume : volume L ≤ ENNReal.ofReal (B ^ n))
    (hinter : ENNReal.ofReal (a ^ n) ≤ volume (K ∩ L)) :
    ∃ t : ℝ, 0 < t ∧ volume (t • L) = 1 ∧
      ENNReal.ofReal ((a / max B 1) ^ n) ≤ volume (K ∩ t • L) := by
  have hLfinite : volume L ≠ ∞ := hL.measure_lt_top.ne
  have hLpos : 0 < volume L :=
    (ENNReal.ofReal_pos.mpr (pow_pos ha n)).trans_le (hinter.trans (measure_mono inter_subset_right))
  let V := (volume L).toReal
  have hV : 0 < V := ENNReal.toReal_pos hLpos.ne' hLfinite
  let s := V ^ ((n : ℝ)⁻¹)
  have hs : 0 < s := Real.rpow_pos_of_pos hV _
  have hspow : s ^ n = V := Real.rpow_inv_natCast_pow hV.le hn.ne'
  let t := s⁻¹
  have ht : 0 < t := inv_pos.mpr hs
  have htpow : t ^ n = V⁻¹ := by dsimp only [t]; rw [inv_pow, hspow]
  have hnorm : volume (t • L) = 1 := by
    rw [Measure.addHaar_smul_of_nonneg volume ht.le,
      finrank_euclideanSpace, Fintype.card_fin, htpow,
      ENNReal.ofReal_inv_of_pos hV]
    dsimp only [V]
    rw [ENNReal.ofReal_toReal hLfinite, ENNReal.inv_mul_cancel hLpos.ne' hLfinite]
  have hmax : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hVB : V ≤ B ^ n := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvolume
    simpa only [ENNReal.toReal_ofReal (pow_nonneg hB.le n)] using h
  have hVmax : V ≤ (max B 1) ^ n := hVB.trans
    (pow_le_pow_left₀ hB.le (le_max_left B 1) n)
  refine ⟨t, ht, hnorm, ?_⟩
  by_cases htOne : t ≤ 1
  · have hconstant : (a / max B 1) ^ n ≤ t ^ n * a ^ n := by
      rw [div_pow, div_eq_mul_inv, htpow]
      have hi : ((max B 1) ^ n)⁻¹ ≤ V⁻¹ :=
        (inv_le_inv₀ (pow_pos hmax n) hV).mpr hVmax
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (pow_nonneg ha.le n)
    calc
      _ ≤ ENNReal.ofReal (t ^ n * a ^ n) := ENNReal.ofReal_le_ofReal hconstant
      _ = ENNReal.ofReal (t ^ n) * ENNReal.ofReal (a ^ n) :=
        ENNReal.ofReal_mul (pow_nonneg ht.le n)
      _ ≤ ENNReal.ofReal (t ^ n) * volume (K ∩ L) := mul_le_mul' le_rfl hinter
      _ ≤ _ := gaussianPosition_shrink_intersection_volume n K L hKconv hKzero t ht.le htOne
  · have hOneT : 1 ≤ t := (lt_of_not_ge htOne).le
    have hsub : K ∩ L ⊆ K ∩ t • L :=
      inter_subset_inter_right K (gaussianPosition_enlarge_convex_set n L hLconv hLzero t ht hOneT)
    have hsmall : a / max B 1 ≤ a := (div_le_iff₀ hmax).mpr (by
      nlinarith [le_max_right B (1 : ℝ)])
    calc
      _ ≤ ENNReal.ofReal (a ^ n) := ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (div_nonneg ha.le hmax.le) hsmall n)
      _ ≤ volume (K ∩ L) := hinter
      _ ≤ _ := measure_mono hsub

theorem gaussianPosition_normalize_origin_ellipsoid (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) (hKeven : ∀ x, -x ∈ K ↔ x ∈ K)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (R : ℝ) (hR : 0 < R) (a B : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hvolume : volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ≤ ENNReal.ofReal (B ^ n))
    (hinter : ENNReal.ofReal (a ^ n) ≤ volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R))) :
    ∃ A' : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      volume (A' '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) = 1 ∧
      ENNReal.ofReal ((a / max B 1) ^ n) ≤
        volume (K ∩ (A' '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) := by
  let L := A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R
  have hKzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ K :=
    interior_subset (symmetric_convex_zero_mem_interior n K hKconv hinterior hKeven)
  have hLcompact : IsCompact L := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).image A.continuous
  have hLconv : Convex ℝ L := (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).linear_image
    A.toLinearEquiv.toLinearMap
  have hLzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ L :=
    ⟨0, by simpa only [mem_closedBall, dist_self] using hR.le, map_zero A⟩
  obtain ⟨t, ht, hnorm, hbound⟩ := gaussianPosition_normalize_convex_intersection n hn K L hKconv
    hKzero hLcompact hLconv hLzero a B ha hB hvolume hinter
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.smulOfNeZero ℝ _ t ht.ne').toContinuousLinearEquiv
  let A' := A.trans T
  have himage : A' '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R = t • L := by
    change (T ∘ A) '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R =
      (fun x => t • x) '' (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
    rw [image_image]
    rfl
  exact ⟨A', by rw [himage]; exact hnorm, by rw [himage]; exact hbound⟩

end AffineFKProof
