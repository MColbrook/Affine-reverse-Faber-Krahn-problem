module

public import AffineFK.BridgeBrownianSegmentIndependence
public import AffineFK.BridgeBrownianSegmentLaws
public import AffineFK.BridgeStartedBrownian

/-!
# Actual product-path composition of killed Brownian endpoint measures

The independent path pieces have their genuine Brownian laws. Survival
is split over the two closed intervals, including the common endpoint.
This supplies a measure-level composition construction; it does not
identify a variational Dirichlet semigroup or select a diagonal by an
almost-everywhere density equality.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

def bridgePathSplit (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n))) :=
  (bridgePastPath n s t ht f, bridgeFutureIncrementPath n s t hs ht f)

theorem bridgePathSplit_measurable (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Measurable (bridgePathSplit n s t hs ht) :=
  (bridgePastPath_measurable n s t ht).prodMk
    (bridgeFutureIncrementPath_measurable n s t hs ht)

theorem bridgeBrownian_split_hasLaw (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    HasLaw (bridgePathSplit n s t hs.le ht.le)
      ((bridgeScaledBrownianLaw n s hs).prod (bridgeScaledBrownianLaw n t ht))
      (bridgeScaledBrownianLaw n (s+t) (add_pos hs ht)) := by
  refine ⟨(bridgePathSplit_measurable n s t hs.le ht.le).aemeasurable, ?_⟩
  exact ((bridgeBrownian_past_future_indep n s t hs ht).map_prod_eq_prod_map_map
    (bridgePastPath_measurable n s t ht.le).aemeasurable
    (bridgeFutureIncrementPath_measurable n s t hs.le ht.le).aemeasurable).trans
    (by rw [(bridgeBrownian_past_hasLaw n s t hs ht).map_eq,
      (bridgeBrownian_future_hasLaw n s t hs ht).map_eq])

def bridgeTranslatePath (n : ℕ) (T : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n))) :
    C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) where
  toFun r := x + f r
  continuous_toFun := continuous_const.add f.continuous

theorem bridgeTranslatePath_joint_measurable (n : ℕ) (T : ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) ×
      C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => bridgeTranslatePath n T p.1 p.2) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  exact measurable_fst.add ((ContinuousMap.measurable_eval r).comp measurable_snd)

def bridgeTranslatedSurvivalSet (n : ℕ) (T : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Set C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) := {f | ∀ r, x + f r ∈ Ω}

theorem bridgeTranslatedSurvivalSet_measurable (n : ℕ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    MeasurableSet (bridgeTranslatedSurvivalSet n T x Ω) :=
  (bridgeFiniteSurvivalSet_isOpen n T Ω hΩ).measurableSet.preimage
    ((bridgeTranslatePath_joint_measurable n T).comp (measurable_const.prodMk measurable_id))

def bridgeComposedSurvivalSet (n : ℕ) (s t : ℝ) (hs : 0 ≤ s)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Set (C(Icc (0 : ℝ) s, EuclideanSpace ℝ (Fin n)) ×
      C(Icc (0 : ℝ) t, EuclideanSpace ℝ (Fin n))) :=
  {p | (∀ r, x+p.1 r ∈ Ω) ∧ (∀ u, x+p.1 ⟨s,hs,le_rfl⟩+p.2 u ∈ Ω)}

theorem bridgeComposedSurvivalSet_measurable (n : ℕ) (s t : ℝ) (hs : 0 ≤ s)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    MeasurableSet (bridgeComposedSurvivalSet n s t hs x Ω) := by
  have hfirst : MeasurableSet {p : C(Icc (0 : ℝ) s, EuclideanSpace ℝ (Fin n)) ×
      C(Icc (0 : ℝ) t, EuclideanSpace ℝ (Fin n)) | ∀ r, x+p.1 r ∈ Ω} :=
    (bridgeTranslatedSurvivalSet_measurable n s x Ω hΩ).preimage measurable_fst
  have hsecond : MeasurableSet {p : C(Icc (0 : ℝ) s, EuclideanSpace ℝ (Fin n)) ×
      C(Icc (0 : ℝ) t, EuclideanSpace ℝ (Fin n)) | ∀ u, x+p.1 ⟨s,hs,le_rfl⟩+p.2 u ∈ Ω} := by
    have hq : Measurable (fun p : C(Icc (0 : ℝ) s, EuclideanSpace ℝ (Fin n)) ×
        C(Icc (0 : ℝ) t, EuclideanSpace ℝ (Fin n)) =>
        (x+p.1 ⟨s,hs,le_rfl⟩,p.2)) :=
      (measurable_const.add ((ContinuousMap.measurable_eval
        (⟨s,hs,le_rfl⟩ : Icc (0 : ℝ) s)).comp measurable_fst)).prodMk measurable_snd
    exact (bridgeFiniteSurvivalSet_isOpen n t Ω hΩ).measurableSet.preimage
      ((bridgeTranslatePath_joint_measurable n t).comp hq)
  exact hfirst.inter hsecond

theorem bridge_survival_split_iff (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n))) :
    f ∈ bridgeTranslatedSurvivalSet n (s+t) x Ω ↔
      bridgePathSplit n s t hs ht f ∈ bridgeComposedSurvivalSet n s t hs x Ω := by
  change (∀ r, x+f r ∈ Ω) ↔
    (∀ r, x+f (bridgePastTime s t ht r) ∈ Ω) ∧
    (∀ u, x+f (bridgeSplitTime s t hs ht) +
      (f (bridgeFutureTime s t hs u)-f (bridgeSplitTime s t hs ht)) ∈ Ω)
  constructor
  · intro h
    refine ⟨fun r => h _, fun u => ?_⟩
    have he : x+f (bridgeSplitTime s t hs ht) +
        (f (bridgeFutureTime s t hs u)-f (bridgeSplitTime s t hs ht)) =
        x+f (bridgeFutureTime s t hs u) := by abel
    rw [he]
    exact h _
  · rintro ⟨hp,hf⟩ r
    by_cases hr : (r:ℝ) ≤ s
    · exact hp ⟨r, r.2.1, hr⟩
    · have hlow : 0 ≤ (r:ℝ)-s := sub_nonneg.mpr (le_of_not_ge hr)
      have hupp : (r:ℝ)-s ≤ t := by have := r.2.2; linarith
      have h := hf ⟨(r:ℝ)-s,hlow,hupp⟩
      have he : bridgeFutureTime s t hs ⟨(r:ℝ)-s,hlow,hupp⟩ = r := by
        apply Subtype.ext
        dsimp [bridgeFutureTime]
        ring
      rw [he] at h
      convert h using 1 <;> abel

end AffineFKProof
