module

public import AffineFK.Geometry
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.Ring

/-!
# Averaging symmetric intersections

The first identity is the nonnegative Tonelli form of the manuscript's
intersection-volume averaging argument. The set in the integrand is
K intersect (x-K), expressed without pointwise-set notation.

This proof reuses Mathlib's Tonelli theorem, invariant-measure translation
formula and indicator integrals. The source headers retain their contributors'
Apache-2.0 attribution.
-/

public section
namespace AffineFKProof
open MeasureTheory Set
open scoped ENNReal Pointwise

/-- The full nonnegative Fubini identity for symmetric intersections, valid
also at infinite measure. -/
theorem intersection_measure_lintegral
    {E : Type*} [AddCommGroup E] [MeasurableSpace E]
    [MeasurableAdd E] [MeasurableSub₂ E]
    (μ : Measure E) [SigmaFinite μ] [Measure.IsAddRightInvariant μ]
    (K : Set E) (hK : MeasurableSet K) :
    (∫⁻ x, μ {y | y ∈ K ∧ x - y ∈ K} ∂μ) = (μ K) ^ 2 := by
  classical
  let F : E → E → ℝ≥0∞ := fun x y => if y ∈ K ∧ x - y ∈ K then 1 else 0
  have hpair : MeasurableSet {p : E × E | p.2 ∈ K ∧ p.1 - p.2 ∈ K} :=
    (hK.preimage measurable_snd).inter
      (hK.preimage (measurable_fst.sub measurable_snd))
  have hF : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun _p : E × E => (1 : ℝ≥0∞)) := measurable_const
    have h0 : Measurable (fun _p : E × E => (0 : ℝ≥0∞)) := measurable_const
    have heq : Function.uncurry F =
        {p : E × E | p.2 ∈ K ∧ p.1 - p.2 ∈ K}.piecewise
          (fun _p => (1 : ℝ≥0∞)) (fun _p => 0) := by
      funext p
      simp only [F, Function.uncurry, Set.piecewise, Set.mem_ofPred_eq]
    rw [heq]
    exact h1.piecewise hpair h0
  have hsection (x : E) :
      μ {y | y ∈ K ∧ x - y ∈ K} = ∫⁻ y, F x y ∂μ := by
    have hs : MeasurableSet {y | y ∈ K ∧ x - y ∈ K} :=
      hK.inter (hK.preimage (measurable_const.sub measurable_id))
    simpa only [F, Set.indicator, Pi.one_apply, Set.mem_ofPred_eq] using
      (lintegral_indicator_one hs).symm
  calc
    _ = ∫⁻ x, ∫⁻ y, F x y ∂μ ∂μ := lintegral_congr hsection
    _ = ∫⁻ y, ∫⁻ x, F x y ∂μ ∂μ := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ y, K.indicator (fun _ => μ K) y ∂μ := by
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ K
      · have heq : (fun x => F x y) = (fun x => K.indicator 1 (x - y)) := by
          funext x
          simp only [F, hy, true_and, Set.indicator, Pi.one_apply]
        rw [heq, lintegral_sub_right_eq_self, lintegral_indicator_one hK]
        simp only [Set.indicator_of_mem hy]
      · simp [F, hy]
    _ = (μ K) ^ 2 := by
      rw [lintegral_indicator_const hK]
      exact (pow_two _).symm

/-- The manuscript's intersection identity for actual Euclidean volume, in its
extended nonnegative form. -/
theorem intersection_volume_lintegral
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) :
    (∫⁻ x, volume {y | y ∈ K ∧ x - y ∈ K}) = (volume K) ^ 2 := by
  exact intersection_measure_lintegral volume K hK

/-- Measurability of the intersection-volume profile, obtained from the
measurable indicator kernel by parameter-dependent integration. -/
theorem measurable_intersection_measure
    {E : Type*} [AddCommGroup E] [MeasurableSpace E]
    [MeasurableAdd E] [MeasurableSub₂ E]
    (μ : Measure E) [SigmaFinite μ]
    (K : Set E) (hK : MeasurableSet K) :
    Measurable (fun x => μ {y | y ∈ K ∧ x - y ∈ K}) := by
  classical
  let F : E → E → ℝ≥0∞ := fun x y => if y ∈ K ∧ x - y ∈ K then 1 else 0
  have hpair : MeasurableSet {p : E × E | p.2 ∈ K ∧ p.1 - p.2 ∈ K} :=
    (hK.preimage measurable_snd).inter
      (hK.preimage (measurable_fst.sub measurable_snd))
  have hF : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun _p : E × E => (1 : ℝ≥0∞)) := measurable_const
    have h0 : Measurable (fun _p : E × E => (0 : ℝ≥0∞)) := measurable_const
    have heq : Function.uncurry F =
        {p : E × E | p.2 ∈ K ∧ p.1 - p.2 ∈ K}.piecewise
          (fun _p => (1 : ℝ≥0∞)) (fun _p => 0) := by
      funext p
      simp only [F, Function.uncurry, Set.piecewise, Set.mem_ofPred_eq]
    rw [heq]
    exact h1.piecewise hpair h0
  have hsection (x : E) :
      (∫⁻ y, F x y ∂μ) = μ {y | y ∈ K ∧ x - y ∈ K} := by
    have hs : MeasurableSet {y | y ∈ K ∧ x - y ∈ K} :=
      hK.inter (hK.preimage (measurable_const.sub measurable_id))
    simpa only [F, Set.indicator, Pi.one_apply, Set.mem_ofPred_eq] using
      lintegral_indicator_one hs
  have houter : Measurable (fun x => ∫⁻ y, F x y ∂μ) := hF.lintegral_prod_right
  simpa only [hsection] using houter

/-- Finite measure makes the profile genuinely integrable, and converts the
nonnegative Tonelli identity to the manuscript's ordinary real integral. -/
theorem intersection_measure_integral
    {E : Type*} [AddCommGroup E] [MeasurableSpace E]
    [MeasurableAdd E] [MeasurableSub₂ E]
    (μ : Measure E) [SigmaFinite μ] [Measure.IsAddRightInvariant μ]
    (K : Set E) (hK : MeasurableSet K) (hfinite : μ K ≠ ∞) :
    Integrable (fun x => (μ {y | y ∈ K ∧ x - y ∈ K}).toReal) μ ∧
      (∫ x, (μ {y | y ∈ K ∧ x - y ∈ K}).toReal ∂μ) = (μ K).toReal ^ 2 := by
  have hmeas := measurable_intersection_measure μ K hK
  have hint : (∫⁻ x, μ {y | y ∈ K ∧ x - y ∈ K} ∂μ) ≠ ∞ := by
    rw [intersection_measure_lintegral μ K hK]
    exact ENNReal.pow_ne_top hfinite
  have hpoint : ∀ᵐ x ∂μ, μ {y | y ∈ K ∧ x - y ∈ K} < ∞ := by
    filter_upwards [] with x
    exact lt_of_le_of_lt (measure_mono (fun _y hy => hy.1))
      (lt_top_iff_ne_top.mpr hfinite)
  refine ⟨integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hint, ?_⟩
  rw [integral_toReal hmeas.aemeasurable hpoint,
    intersection_measure_lintegral μ K hK, ENNReal.toReal_pow]

/-- For a compact Euclidean set the profile is integrable and its real integral
is exactly the square of the set's volume. Convexity and positive volume are
unnecessary for this identity. -/
theorem intersection_volume_integral
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    Integrable (fun x => (volume {y | y ∈ K ∧ x - y ∈ K}).toReal) volume ∧
      (∫ x, (volume {y | y ∈ K ∧ x - y ∈ K}).toReal) =
        (volume K).toReal ^ 2 := by
  exact intersection_measure_integral volume K hK.measurableSet hK.measure_ne_top

/-- Averaging over any finite positive-measure support of the intersection
profile produces an intersection at least as large as its exact mean. -/
theorem exists_intersection_measure_ge_average
    {E : Type*} [AddCommGroup E] [MeasurableSpace E]
    [MeasurableAdd E] [MeasurableSub₂ E]
    (μ : Measure E) [SigmaFinite μ] [Measure.IsAddRightInvariant μ]
    (K : Set E) (hK : MeasurableSet K) (hKfinite : μ K ≠ ∞)
    (S : Set E) (hS : MeasurableSet S) (hSpos : μ S ≠ 0) (hSfinite : μ S ≠ ∞)
    (hsupport : ∀ x ∉ S, μ {y | y ∈ K ∧ x - y ∈ K} = 0) :
    ∃ x, (μ K) ^ 2 / μ S ≤ μ {y | y ∈ K ∧ x - y ∈ K} := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ S) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hSpos hSfinite
  have heq : S.indicator (fun x => μ {y | y ∈ K ∧ x - y ∈ K}) =
      (fun x => μ {y | y ∈ K ∧ x - y ∈ K}) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, hsupport x hx]
  have htotal :
      (∫⁻ x, μ {y | y ∈ K ∧ x - y ∈ K} ∂ProbabilityTheory.cond μ S) =
        (μ S)⁻¹ * (μ K) ^ 2 := by
    rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
      ← lintegral_indicator hS, heq, intersection_measure_lintegral μ K hK]
  have hint :
      (∫⁻ x, μ {y | y ∈ K ∧ x - y ∈ K} ∂ProbabilityTheory.cond μ S) ≠ ∞ := by
    rw [htotal]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hSpos) (ENNReal.pow_ne_top hKfinite)
  obtain ⟨x, hx⟩ := exists_lintegral_le hint
  refine ⟨x, ?_⟩
  simpa only [htotal, ENNReal.div_eq_inv_mul] using hx

/-- A sum of two points of a convex set belongs to its double dilate. -/
theorem add_mem_double_of_mem
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (hK : Convex ℝ K) (x y : E) (hx : x ∈ K) (hy : y ∈ K) :
    x + y ∈ (2 : ℝ) • K := by
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ K :=
    hK hx hy (by norm_num) (by norm_num) (by norm_num)
  refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y, hmid, ?_⟩
  simp only [smul_add, smul_smul]
  norm_num

/-- The exact Minkowski-sum identity used to locate the intersection profile's
support. -/
theorem convex_add_self_eq_double
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (hK : Convex ℝ K) :
    K + K = (2 : ℝ) • K := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, y, hy, rfl⟩
    exact add_mem_double_of_mem K hK x y hx hy
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨x, hx, x, hx, ?_⟩
    simp only [two_smul]

/-- Outside the double dilate, the symmetric intersection is empty. No
assumption that the original body contains the origin is needed. -/
theorem intersection_empty_outside_double
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (hK : Convex ℝ K) (x : E) (hx : x ∉ (2 : ℝ) • K) :
    {y | y ∈ K ∧ x - y ∈ K} = ∅ := by
  apply Set.Subset.antisymm
  · intro y hy
    have hsum := add_mem_double_of_mem K hK y (x - y) hy.1 hy.2
    have heq : y + (x - y) = x := by abel
    rw [heq] at hsum
    exact (hx hsum).elim
  · exact Set.empty_subset _

/-- Doubling a Euclidean set multiplies its actual volume by exactly 2^n. -/
theorem volume_double_set
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) :
    volume ((2 : ℝ) • K) = (2 : ℝ≥0∞) ^ n * volume K := by
  simp [ENNReal.ofReal_pow]

/-- The large-intersection assertion with its exact dimension-dependent
constant, using actual Euclidean volume and no origin-symmetry assumption. -/
theorem exists_large_intersection_volume
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact K) (hK : Convex ℝ K) (hpos : 0 < volume K) :
    ∃ x, volume K / (2 : ℝ≥0∞) ^ n ≤ volume {y | y ∈ K ∧ x - y ∈ K} := by
  have hdouble : IsCompact ((2 : ℝ) • K) := IsCompact.smul 2 hcompact
  have hSpos : volume ((2 : ℝ) • K) ≠ 0 := by
    rw [volume_double_set n K]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hpos.ne'
  have hsupp : ∀ x ∉ (2 : ℝ) • K, volume {y | y ∈ K ∧ x - y ∈ K} = 0 := by
    intro x hx
    rw [intersection_empty_outside_double K hK x hx, measure_empty]
  obtain ⟨x, hx⟩ := exists_intersection_measure_ge_average volume K
    hcompact.measurableSet hcompact.measure_ne_top ((2 : ℝ) • K)
    hdouble.measurableSet hSpos hdouble.measure_ne_top hsupp
  rw [volume_double_set n K] at hx
  have hid : (volume K) ^ 2 / ((2 : ℝ≥0∞) ^ n * volume K) =
      volume K / (2 : ℝ≥0∞) ^ n := by
    rw [pow_two, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inr hcompact.measure_ne_top) (Or.inr hpos.ne'),
      ENNReal.div_eq_inv_mul]
    calc
      _ = ((2 : ℝ≥0∞) ^ n)⁻¹ * (((volume K)⁻¹ * volume K) * volume K) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hpos.ne' hcompact.measure_ne_top, one_mul]
  exact ⟨x, hid ▸ hx⟩

/-- The same large-intersection estimate in the manuscript's real-valued
volume notation, with every volume conversion justified by compactness. -/
theorem exists_large_intersection_real_volume
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact K) (hK : Convex ℝ K) (hpos : 0 < volume K) :
    ∃ x, (volume K).toReal / (2 : ℝ) ^ n ≤
      (volume {y | y ∈ K ∧ x - y ∈ K}).toReal := by
  obtain ⟨x, hx⟩ := exists_large_intersection_volume n K hcompact hK hpos
  have hfinite : volume {y | y ∈ K ∧ x - y ∈ K} ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono (fun _y hy => hy.1)) hcompact.measure_lt_top).ne
  exact ⟨x, by simpa using ENNReal.toReal_mono hfinite hx⟩

/-- Positive Euclidean volume forces a convex set to have nonempty interior.
The proof reuses Oliver Nash's affine-span criterion and Mathlib's zero-measure
theorem for proper affine subspaces. -/
theorem convex_positive_volume_interior_nonempty
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : Convex ℝ K) (hpos : 0 < volume K) :
    (interior K).Nonempty := by
  apply hK.interior_nonempty_iff_affineSpan_eq_top.mpr
  by_contra hspan
  have hzero : volume K = 0 :=
    measure_mono_null (subset_affineSpan ℝ K)
      (Measure.addHaar_affineSubspace volume (affineSpan ℝ K) hspan)
  exact hpos.ne' hzero

/-- The centre of an even convex set of positive volume lies in its interior. -/
theorem zero_mem_interior_convex_even
    (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (hD : Convex ℝ D) (heven : ∀ z ∈ D, -z ∈ D) (hpos : 0 < volume D) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ interior D := by
  obtain ⟨x, hx⟩ := convex_positive_volume_interior_nonempty n D hD hpos
  have h := hD.combo_interior_self_mem_interior hx (heven x (interior_subset hx))
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simpa only [smul_neg, add_neg_cancel] using h

/-- The symmetric intersection is compact when the original set is compact. -/
theorem isCompact_symmetric_intersection
    {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (hK : IsCompact K) (x : E) :
    IsCompact {y | y ∈ K ∧ x - y ∈ K} := by
  change IsCompact (K ∩ (fun y => x - y) ⁻¹' K)
  exact hK.inter_right (hK.isClosed.preimage (continuous_const.sub continuous_id))

/-- Convexity of the symmetric intersection. -/
theorem convex_symmetric_intersection
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (hK : Convex ℝ K) (x : E) :
    Convex ℝ {y | y ∈ K ∧ x - y ∈ K} := by
  intro u hu v hv a b ha hb hab
  refine ⟨hK hu.1 hv.1 ha hb hab, ?_⟩
  have h := hK hu.2 hv.2 ha hb hab
  have heq : a • (x - u) + b • (x - v) = x - (a • u + b • v) := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
  rwa [heq] at h

/-- Reflection about x/2 preserves the intersection. -/
theorem symmetric_intersection_reflection
    {E : Type*} [AddCommGroup E]
    (K : Set E) (x y : E) :
    (y ∈ {z | z ∈ K ∧ x - z ∈ K}) ↔
      (x - y ∈ {z | z ∈ K ∧ x - z ∈ K}) := by
  constructor
  · rintro ⟨hy, hxy⟩
    exact ⟨hxy, by simpa only [sub_sub_cancel] using hy⟩
  · rintro ⟨hxy, hy⟩
    exact ⟨by simpa only [sub_sub_cancel] using hy, hxy⟩

/-- Compactness of the centred intersection follows from translation and a
closed reflected preimage. -/
theorem isCompact_centered_intersection
    {E : Type*} [NormedAddCommGroup E]
    (K : Set E) (hK : IsCompact K) (c : E) :
    IsCompact {z | z + c ∈ K ∧ c - z ∈ K} := by
  have heq : {z | z + c ∈ K} = (fun y => y - c) '' K := by
    ext z
    constructor
    · intro hz
      exact ⟨z + c, hz, add_sub_cancel_right z c⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [Set.mem_ofPred_eq, sub_add_cancel] using hy
  have hfirst : IsCompact {z | z + c ∈ K} := by
    rw [heq]
    exact hK.image (continuous_id.sub continuous_const)
  change IsCompact ({z | z + c ∈ K} ∩ (fun z => c - z) ⁻¹' K)
  exact hfirst.inter_right (hK.isClosed.preimage (continuous_const.sub continuous_id))

/-- The centred intersection is exactly the translate of K intersect (2c-K). -/
theorem centered_intersection_eq_translate
    {E : Type*} [AddCommGroup E]
    (K : Set E) (c : E) :
    {z | z + c ∈ K ∧ c - z ∈ K} =
      (fun y => y - c) '' {y | y ∈ K ∧ (c + c) - y ∈ K} := by
  ext z
  constructor
  · intro hz
    refine ⟨z + c, ⟨hz.1, ?_⟩, add_sub_cancel_right z c⟩
    have heq : (c + c) - (z + c) = c - z := by abel
    rw [heq]
    exact hz.2
  · rintro ⟨y, hy, rfl⟩
    refine ⟨by simpa only [sub_add_cancel] using hy.1, ?_⟩
    have heq : c - (y - c) = (c + c) - y := by abel
    rw [heq]
    exact hy.2

/-- Centring preserves actual Haar measure. -/
theorem centered_intersection_measure_eq
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddRightInvariant μ]
    (K : Set E) (c : E) :
    μ {z | z + c ∈ K ∧ c - z ∈ K} =
      μ {y | y ∈ K ∧ (c + c) - y ∈ K} := by
  have heq : {z | z + c ∈ K ∧ c - z ∈ K} =
      (fun z => z + c) ⁻¹' {y | y ∈ K ∧ (c + c) - y ∈ K} := by
    ext z
    have hsub : (c + c) - (z + c) = c - z := by abel
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hsub]
  rw [heq, measure_preimage_add_right]

/-- The complete compact, convex and full-dimensional symmetric-subbody
construction used in the final reduction. Both intersection sets and their
translation relation are specified explicitly. -/
theorem symmetric_subbody_construction
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact K) (hK : Convex ℝ K) (hpos : 0 < volume K) :
    ∃ x c : EuclideanSpace ℝ (Fin n),
      ∃ L D : Set (EuclideanSpace ℝ (Fin n)),
      c + c = x ∧ L = {y | y ∈ K ∧ x - y ∈ K} ∧
      D = {z | z + c ∈ K ∧ c - z ∈ K} ∧
      IsCompact L ∧ Convex ℝ L ∧ (interior L).Nonempty ∧ L ⊆ K ∧
      (∀ y, y ∈ L ↔ x - y ∈ L) ∧
      IsCompact D ∧ Convex ℝ D ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ interior D ∧
      (∀ z, z ∈ D ↔ -z ∈ D) ∧
      D = (fun y => y - c) '' L ∧ volume D = volume L ∧
      (volume K).toReal / (2 : ℝ) ^ n ≤ (volume L).toReal := by
  obtain ⟨x, hbound⟩ := exists_large_intersection_volume n K hcompact hK hpos
  let c := (1 / 2 : ℝ) • x
  let L := {y | y ∈ K ∧ x - y ∈ K}
  let D := {z | z + c ∈ K ∧ c - z ∈ K}
  have hcc : c + c = x := by
    dsimp [c]
    rw [← add_smul]
    norm_num
  have hLcompact : IsCompact L := isCompact_symmetric_intersection K hcompact x
  have hLconvex : Convex ℝ L := convex_symmetric_intersection K hK x
  have hLpos : 0 < volume L :=
    (ENNReal.div_pos hpos.ne' (ENNReal.pow_ne_top (by norm_num))).trans_le hbound
  have hDcompact : IsCompact D := isCompact_centered_intersection K hcompact c
  have hDconvex : Convex ℝ D := convex_centered_intersection hK c
  have hDvolume : volume D = volume L := by
    change volume {z | z + c ∈ K ∧ c - z ∈ K} =
      volume {y | y ∈ K ∧ x - y ∈ K}
    rw [centered_intersection_measure_eq volume K c, hcc]
  have heven : ∀ z ∈ D, -z ∈ D :=
    fun z hz => (centered_intersection_even K c z).2 hz
  have hDinterior : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior D :=
    zero_mem_interior_convex_even n D hDconvex heven (hDvolume.symm ▸ hLpos)
  have htranslate : D = (fun y => y - c) '' L := by
    change {z | z + c ∈ K ∧ c - z ∈ K} =
      (fun y => y - c) '' {y | y ∈ K ∧ x - y ∈ K}
    rw [centered_intersection_eq_translate K c, hcc]
  refine ⟨x, c, L, D, hcc, rfl, rfl, hLcompact, hLconvex,
    convex_positive_volume_interior_nonempty n L hLconvex hLpos,
    (fun _y hy => hy.1), (fun y => symmetric_intersection_reflection K x y),
    hDcompact, hDconvex, hDinterior,
    (fun z => (centered_intersection_even K c z).symm), htranslate, hDvolume, ?_⟩
  simpa using ENNReal.toReal_mono hLcompact.measure_ne_top hbound

/-- The original convex-body interior hypothesis implies positive volume. -/
theorem volume_pos_of_interior_nonempty
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (hinterior : (interior K).Nonempty) :
    0 < volume K := by
  exact (isOpen_interior.measure_pos volume hinterior).trans_le (measure_mono interior_subset)

/-- Every full-dimensional compact convex set contains a centrally symmetric
full-dimensional compact convex subset of volume at least 2^(-n) times its
own volume. This uses the manuscript's original convex-body hypotheses. -/
theorem exists_large_symmetric_convex_subbody
    (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact K) (hK : Convex ℝ K) (hinterior : (interior K).Nonempty) :
    ∃ c : EuclideanSpace ℝ (Fin n), ∃ L : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact L ∧ Convex ℝ L ∧ (interior L).Nonempty ∧ L ⊆ K ∧
      (∀ y, y ∈ L ↔ (c + c) - y ∈ L) ∧
      (volume K).toReal / (2 : ℝ) ^ n ≤ (volume L).toReal := by
  obtain ⟨x, c, L, D, hcc, _hL, _hD, hLc, hLv, hLi, hLs, hSym,
      _hDc, _hDv, _hDi, _hDs, _hDt, _hVD, hbound⟩ :=
    symmetric_subbody_construction n K hcompact hK (volume_pos_of_interior_nonempty n K hinterior)
  refine ⟨c, L, hLc, hLv, hLi, hLs, ?_, hbound⟩
  intro y
  simpa only [hcc] using hSym y

end AffineFKProof
