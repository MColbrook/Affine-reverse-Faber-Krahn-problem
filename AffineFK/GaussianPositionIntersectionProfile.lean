module

public import AffineFK.GaussianPositionPoincare
public import AffineFK.EuclideanLogConcavity
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# The central maximum of the actual intersection-volume function

For centrally symmetric convex sets, the intersection with any translate
has volume at most the central intersection. This is the assertion of
Klartag's ETH 2025 Lecture 7, Lemma 7.5. Here the proof uses the already
proved genuine Prekopa convolution theorem for indicator functions;
evenness and log-concavity then give the central maximum. No existence
of an M-ellipsoid or universal covering estimate is inferred.

Primary source: https://www.weizmann.ac.il/math/klartag/sites/math.klartag/files/uploads/lecture7_101125.pdf
Mathlib's actual Haar reflection invariance and nonnegative indicator
integrals retain their Apache-2.0 source contributor attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped ENNReal

def gaussianPositionIntersectionProfile (n : ℕ)
    (K L : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  volume (K ∩ {x | x - z ∈ L})

theorem gaussianPosition_intersection_translate_image (n : ℕ)
    (K L : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    K ∩ {x | x - z ∈ L} = K ∩ ((fun y => z + y) '' L) := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hx, ⟨x - z, hy, by abel⟩⟩
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨hx, ?_⟩
    change z + y - z ∈ L
    simpa only [add_sub_cancel_left] using hy

theorem gaussianPositionIntersectionProfile_zero (n : ℕ)
    (K L : Set (EuclideanSpace ℝ (Fin n))) :
    gaussianPositionIntersectionProfile n K L 0 = volume (K ∩ L) := by
  simp only [gaussianPositionIntersectionProfile, sub_zero, Set.ofPred_mem_eq]

theorem gaussianPositionIntersectionProfile_eq_convolution (n : ℕ)
    (K L : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (hL : MeasurableSet L)
    (hLeven : ∀ x, -x ∈ L ↔ x ∈ L) (z : EuclideanSpace ℝ (Fin n)) :
    gaussianPositionIntersectionProfile n K L z =
      ∫⁻ y, L.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (z - y) *
        K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y := by
  classical
  have heq : (fun y : EuclideanSpace ℝ (Fin n) => L.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
        (z - y) * K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y) =
      (K ∩ {y | y - z ∈ L}).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) := by
    funext y
    have hy : z - y ∈ L ↔ y - z ∈ L := by simpa only [neg_sub] using hLeven (y - z)
    by_cases hyK : y ∈ K <;> by_cases hyL : y - z ∈ L <;>
      simp [Set.indicator, hy, hyK, hyL]
  have hset : MeasurableSet (K ∩ {y : EuclideanSpace ℝ (Fin n) | y - z ∈ L}) :=
    hK.inter (hL.preimage (show Measurable (fun y : EuclideanSpace ℝ (Fin n) => y - z) by fun_prop))
  rw [heq]
  exact (lintegral_indicator_one hset).symm

theorem gaussianPositionIntersectionProfile_logConcave (n : ℕ)
    (K L : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (hL : MeasurableSet L)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L) (hLeven : ∀ x, -x ∈ L ↔ x ∈ L) :
    LogConcaveDensity (gaussianPositionIntersectionProfile n K L) := by
  have heq : gaussianPositionIntersectionProfile n K L = fun z =>
      ∫⁻ y, L.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (z - y) *
        K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y :=
    funext (gaussianPositionIntersectionProfile_eq_convolution n K L hK hL hLeven)
  rw [heq]
  exact logConcaveDensity_convolution_euclidean n _ _
    (measurable_const.indicator hL) (measurable_const.indicator hK)
    (gaussianPosition_logConcave_indicator_const L hLconv 1)
    (gaussianPosition_logConcave_indicator_const K hKconv 1)

theorem gaussianPositionIntersectionProfile_even (n : ℕ)
    (K L : Set (EuclideanSpace ℝ (Fin n)))
    (hKeven : ∀ x, -x ∈ K ↔ x ∈ K) (hLeven : ∀ x, -x ∈ L ↔ x ∈ L)
    (z : EuclideanSpace ℝ (Fin n)) :
    gaussianPositionIntersectionProfile n K L (-z) = gaussianPositionIntersectionProfile n K L z := by
  have heq : Neg.neg ⁻¹' (K ∩ {x | x - z ∈ L}) = K ∩ {x | x + z ∈ L} := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hKeven]
    have hx : -x - z = -(x + z) := by abel
    rw [hx, hLeven]
  calc
    _ = volume (K ∩ {x | x + z ∈ L}) := by simp only [gaussianPositionIntersectionProfile, sub_neg_eq_add]
    _ = volume (Neg.neg ⁻¹' (K ∩ {x | x - z ∈ L})) := congrArg volume heq.symm
    _ = _ := Measure.measure_preimage_neg volume _

theorem gaussianPositionIntersectionProfile_le_zero (n : ℕ)
    (K L : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) (hL : MeasurableSet L)
    (hKconv : Convex ℝ K) (hLconv : Convex ℝ L)
    (hKeven : ∀ x, -x ∈ K ↔ x ∈ K) (hLeven : ∀ x, -x ∈ L ↔ x ∈ L)
    (z : EuclideanSpace ℝ (Fin n)) :
    gaussianPositionIntersectionProfile n K L z ≤ volume (K ∩ L) := by
  have h := gaussianPositionIntersectionProfile_logConcave n K L hK hL hKconv hLconv hLeven
    (1 / 2) (by norm_num) (by norm_num) z (-z)
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  rw [smul_neg, add_neg_cancel,
    gaussianPositionIntersectionProfile_even n K L hKeven hLeven z,
    ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)] at h
  norm_num only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.rpow_one] at h
  simpa only [gaussianPositionIntersectionProfile_zero] using h

end AffineFKProof
