module

public import AffineFK.BridgeStartedBrownian
public import Mathlib.Topology.ContinuousMap.Interval

/-!
# Constructing two independent short bridges and their Gaussian middle point

Both bridge inputs are the actual coefficient constructions, whose
endpoints are zero for every coefficient array. Consequently the two
continuous pieces agree at the splitting time for every sample; no
exceptional-set continuity or conditional Gaussian law is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

/-- Two independent actual bridge coefficient arrays and one independent
standard Gaussian vector, for a centered bridge split at a middle time. -/
abbrev BridgeMiddleSample (n : ℕ) :=
  (((∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n)) ×
    (∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n))) × EuclideanSpace ℝ (Fin n))

/-- The actual three-factor product probability supplying the two bridges
and the independent standard Gaussian middle-point vector. -/
def bridgeMiddleMeasure (n : ℕ) : Measure (BridgeMiddleSample n) :=
  ((bridgeCoefficientMeasure n).prod (bridgeCoefficientMeasure n)).prod
    (stdGaussian (EuclideanSpace ℝ (Fin n)))

instance bridgeMiddleMeasure_probability (n : ℕ) : IsProbabilityMeasure (bridgeMiddleMeasure n) := by
  unfold bridgeMiddleMeasure
  infer_instance

/-- The standard deviation of the centered middle point for durations
`s,t`; its actual variance for positive durations is `s*t/(s+t)`. -/
def bridgeMiddleScale (s t : ℝ) : ℝ := Real.sqrt (s*t/(s+t))

theorem bridgeMiddleScale_sq (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (bridgeMiddleScale s t)^2 = s*t/(s+t) :=
  Real.sq_sqrt (by exact div_nonneg (mul_nonneg hs.le ht.le) (add_pos hs ht).le)

/-- Normalized time `(r-s)/t` on the second closed interval `[s,s+t]`. -/
def bridgePostUnitTime (s t : ℝ) (ht : 0 < t) (r : Icc s (s+t)) : Icc (0 : ℝ) 1 :=
  ⟨((r:ℝ)-s)/t, div_nonneg (sub_nonneg.mpr r.2.1) ht.le,
    (div_le_one ht).mpr (by have := r.2.2; linarith)⟩

theorem bridgePostUnitTime_continuous (s t : ℝ) (ht : 0 < t) :
    Continuous (bridgePostUnitTime s t ht) :=
  (((continuous_subtype_val.sub continuous_const).div_const t).subtype_mk _)

theorem bridgePostUnitTime_start (s t : ℝ) (ht : 0 < t) :
    bridgePostUnitTime s t ht ⟨s,le_rfl,le_add_of_nonneg_right ht.le⟩ =
      (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1) := by
  apply Subtype.ext
  change (s-s)/t = 0
  simp

theorem bridgePostUnitTime_end (s t : ℝ) (ht : 0 < t) :
    bridgePostUnitTime s t ht ⟨s+t,le_add_of_nonneg_right ht.le,le_rfl⟩ =
      (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1) := by
  apply Subtype.ext
  change (s+t-s)/t = 1
  rw [add_sub_cancel_left, div_self ht.ne']

/-- The first actual bridge, dilated to duration `s` and connected to the
actual Gaussian middle point by its linear interpolation. -/
def bridgeSplitLeftPath (n : ℕ) (s t : ℝ) (hs : 0 < s) (p : BridgeMiddleSample n) :
    C(Icc (0 : ℝ) s, EuclideanSpace ℝ (Fin n)) where
  toFun r := Real.sqrt s • bridgeContinuousSeries n p.1.1 (bridgeUnitTime s hs r) +
    ((r:ℝ)/s) • (bridgeMiddleScale s t • p.2)
  continuous_toFun := by
    exact (((bridgeContinuousSeries n p.1.1).continuous.comp
      (bridgeUnitTime_continuous s hs)).const_smul (Real.sqrt s)).add
      ((continuous_subtype_val.div_const s).smul (continuous_const (y := bridgeMiddleScale s t • p.2)))

/-- The second actual bridge, dilated to duration `t` and linearly
connected from the same Gaussian middle point to the zero final point. -/
def bridgeSplitRightPath (n : ℕ) (s t : ℝ) (ht : 0 < t) (p : BridgeMiddleSample n) :
    C(Icc s (s+t), EuclideanSpace ℝ (Fin n)) where
  toFun r := Real.sqrt t • bridgeContinuousSeries n p.1.2 (bridgePostUnitTime s t ht r) +
    (1-(bridgePostUnitTime s t ht r:ℝ)) • (bridgeMiddleScale s t • p.2)
  continuous_toFun := by
    exact (((bridgeContinuousSeries n p.1.2).continuous.comp
      (bridgePostUnitTime_continuous s t ht)).const_smul (Real.sqrt t)).add
      (((continuous_const (y := (1:ℝ))).sub (continuous_subtype_val.comp
        (bridgePostUnitTime_continuous s t ht))).smul (continuous_const (y := bridgeMiddleScale s t • p.2)))

theorem bridgeSplitLeftPath_end (n : ℕ) (s t : ℝ) (hs : 0 < s) (p : BridgeMiddleSample n) :
    bridgeSplitLeftPath n s t hs p ⟨s,hs.le,le_rfl⟩ = bridgeMiddleScale s t • p.2 := by
  change Real.sqrt s • bridgeContinuousSeries n p.1.1 (bridgeUnitTime s hs ⟨s,hs.le,le_rfl⟩) +
    (s/s) • (bridgeMiddleScale s t • p.2) = _
  rw [bridgeUnitTime_terminal, bridgeContinuousSeries_one, smul_zero, div_self hs.ne', one_smul, zero_add]

theorem bridgeSplitRightPath_start (n : ℕ) (s t : ℝ) (ht : 0 < t) (p : BridgeMiddleSample n) :
    bridgeSplitRightPath n s t ht p ⟨s,le_rfl,le_add_of_nonneg_right ht.le⟩ =
      bridgeMiddleScale s t • p.2 := by
  change Real.sqrt t • bridgeContinuousSeries n p.1.2 (bridgePostUnitTime s t ht _) +
    (1-(bridgePostUnitTime s t ht _:ℝ)) • (bridgeMiddleScale s t • p.2) = _
  rw [bridgePostUnitTime_start, bridgeContinuousSeries_zero, smul_zero]
  simp

/-- The genuine continuous centered bridge assembled from the two actual
independent short bridges and their common actual Gaussian middle point. -/
def bridgeSplitCenteredPath (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (p : BridgeMiddleSample n) : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n)) := by
  letI : Fact ((0:ℝ) ≤ s) := ⟨hs.le⟩
  letI : Fact (s ≤ s+t) := ⟨le_add_of_nonneg_right ht.le⟩
  exact ContinuousMap.concat (bridgeSplitLeftPath n s t hs p) (bridgeSplitRightPath n s t ht p)

theorem bridgeSplitCenteredPath_left (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (p : BridgeMiddleSample n) (r : Icc (0 : ℝ) (s+t)) (hr : (r:ℝ) ≤ s) :
    bridgeSplitCenteredPath n s t hs ht p r = bridgeSplitLeftPath n s t hs p ⟨r,r.2.1,hr⟩ := by
  letI : Fact ((0:ℝ) ≤ s) := ⟨hs.le⟩
  letI : Fact (s ≤ s+t) := ⟨le_add_of_nonneg_right ht.le⟩
  apply ContinuousMap.concat_left ?_ hr
  change bridgeSplitLeftPath n s t hs p ⟨s,hs.le,le_rfl⟩ =
    bridgeSplitRightPath n s t ht p ⟨s,le_rfl,le_add_of_nonneg_right ht.le⟩
  rw [bridgeSplitLeftPath_end, bridgeSplitRightPath_start]

theorem bridgeSplitCenteredPath_right (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (p : BridgeMiddleSample n) (r : Icc (0 : ℝ) (s+t)) (hr : s ≤ (r:ℝ)) :
    bridgeSplitCenteredPath n s t hs ht p r = bridgeSplitRightPath n s t ht p ⟨r,hr,r.2.2⟩ := by
  letI : Fact ((0:ℝ) ≤ s) := ⟨hs.le⟩
  letI : Fact (s ≤ s+t) := ⟨le_add_of_nonneg_right ht.le⟩
  apply ContinuousMap.concat_right ?_ hr
  change bridgeSplitLeftPath n s t hs p ⟨s,hs.le,le_rfl⟩ =
    bridgeSplitRightPath n s t ht p ⟨s,le_rfl,le_add_of_nonneg_right ht.le⟩
  rw [bridgeSplitLeftPath_end, bridgeSplitRightPath_start]

end AffineFKProof
