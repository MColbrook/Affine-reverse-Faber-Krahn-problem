module

public import AffineFK.BridgeMiddleConstruction

/-!
# Measurability of the actual Gaussian-middle continuous-path construction
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridgeSplitLeftPath_measurable (n : ℕ) (s t : ℝ) (hs : 0 < s) :
    Measurable (bridgeSplitLeftPath n s t hs) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  have hb : Measurable (fun p : BridgeMiddleSample n =>
      bridgeContinuousSeries n p.1.1 (bridgeUnitTime s hs r)) :=
    ((ContinuousMap.measurable_eval _).comp (bridgeContinuousSeries_measurable n)).comp
      (measurable_fst.comp measurable_fst)
  have hz : Measurable (fun p : BridgeMiddleSample n => bridgeMiddleScale s t • p.2) :=
    measurable_snd.const_smul (bridgeMiddleScale s t)
  exact (hb.const_smul (Real.sqrt s)).add (hz.const_smul ((r:ℝ)/s))

theorem bridgeSplitRightPath_measurable (n : ℕ) (s t : ℝ) (ht : 0 < t) :
    Measurable (bridgeSplitRightPath n s t ht) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  have hb : Measurable (fun p : BridgeMiddleSample n =>
      bridgeContinuousSeries n p.1.2 (bridgePostUnitTime s t ht r)) :=
    ((ContinuousMap.measurable_eval _).comp (bridgeContinuousSeries_measurable n)).comp
      (measurable_snd.comp measurable_fst)
  have hz : Measurable (fun p : BridgeMiddleSample n => bridgeMiddleScale s t • p.2) :=
    measurable_snd.const_smul (bridgeMiddleScale s t)
  exact (hb.const_smul (Real.sqrt t)).add (hz.const_smul (1-(bridgePostUnitTime s t ht r:ℝ)))

theorem bridgeSplitCenteredPath_measurable (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Measurable (bridgeSplitCenteredPath n s t hs ht) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  by_cases hr : (r:ℝ) ≤ s
  · have he : (fun p => bridgeSplitCenteredPath n s t hs ht p r) =
        fun p => bridgeSplitLeftPath n s t hs p ⟨r,r.2.1,hr⟩ := by
      funext p
      exact bridgeSplitCenteredPath_left n s t hs ht p r hr
    rw [he]
    exact (ContinuousMap.measurable_eval _).comp (bridgeSplitLeftPath_measurable n s t hs)
  · have he : (fun p => bridgeSplitCenteredPath n s t hs ht p r) =
        fun p => bridgeSplitRightPath n s t ht p ⟨r,(le_of_not_ge hr),r.2.2⟩ := by
      funext p
      exact bridgeSplitCenteredPath_right n s t hs ht p r (le_of_not_ge hr)
    rw [he]
    exact (ContinuousMap.measurable_eval _).comp (bridgeSplitRightPath_measurable n s t ht)

end AffineFKProof
