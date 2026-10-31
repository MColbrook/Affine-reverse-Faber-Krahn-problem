module

public import AffineFK.BridgeKilledComposition

/-!
# Composition of genuine killed endpoint measures through independent paths

The actual Brownian split law, rather than an assumed Markov kernel,
identifies the long killed endpoint measure with the explicit product
of its shorter Brownian paths restricted to both survival events.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridgeStartedBrownianLaw_eq_translate (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) :
    bridgeStartedBrownianLaw n T hT x =
      (bridgeScaledBrownianLaw n T hT).map (bridgeTranslatePath n T x) := by
  have hm : Measurable (bridgeTranslatePath n T x) :=
    (bridgeTranslatePath_joint_measurable n T).comp (measurable_const.prodMk measurable_id)
  rw [bridgeStartedBrownianLaw, bridgeScaledBrownianLaw,
    Measure.map_map hm (bridgeScaledBrownianPath_measurable n T hT)]
  rfl

def bridgeTranslatedKilledEndpointMeasure (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) :=
  ((bridgeScaledBrownianLaw n T hT).restrict (bridgeTranslatedSurvivalSet n T x Ω)).map
    (fun f => x + f ⟨T,hT.le,le_rfl⟩)

theorem bridgeTranslatedKilledEndpointMeasure_eq_started (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeTranslatedKilledEndpointMeasure n T hT x Ω =
      bridgeStartedKilledEndpointMeasure n T hT x Ω := by
  have hm : Measurable (bridgeTranslatePath n T x) :=
    (bridgeTranslatePath_joint_measurable n T).comp (measurable_const.prodMk measurable_id)
  have he : Measurable (fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) =>
      x+f ⟨T,hT.le,le_rfl⟩) := measurable_const.add (ContinuousMap.measurable_eval _)
  apply Measure.ext
  intro S hS
  rw [bridgeTranslatedKilledEndpointMeasure, Measure.map_apply he hS,
    Measure.restrict_apply (hS.preimage he), bridgeStartedKilledEndpointMeasure,
    Measure.map_apply (ContinuousMap.measurable_eval _) hS,
    Measure.restrict_apply (hS.preimage (ContinuousMap.measurable_eval _)),
    bridgeStartedBrownianLaw_eq_translate,
    Measure.map_apply hm ((hS.preimage (ContinuousMap.measurable_eval _)).inter
      (bridgeFiniteSurvivalSet_isOpen n T Ω hΩ).measurableSet)]
  rfl

def bridgeProductKilledEndpointMeasure (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) :=
  (((bridgeScaledBrownianLaw n s hs).prod (bridgeScaledBrownianLaw n t ht)).restrict
    (bridgeComposedSurvivalSet n s t hs.le x Ω)).map
      (fun p => x+p.1 ⟨s,hs.le,le_rfl⟩+p.2 ⟨t,ht.le,le_rfl⟩)

theorem bridgePathSplit_terminal (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n))) :
    (bridgePathSplit n s t hs ht f).1 ⟨s,hs,le_rfl⟩ +
      (bridgePathSplit n s t hs ht f).2 ⟨t,ht,le_rfl⟩ =
        f ⟨s+t,add_nonneg hs ht,le_rfl⟩ := by
  change f ⟨s,hs,le_add_of_nonneg_right ht⟩ +
    (f ⟨s+t,add_nonneg hs ht,le_rfl⟩ - f ⟨s,hs,le_add_of_nonneg_right ht⟩) = _
  abel

theorem bridgeStartedKilledEndpointMeasure_eq_product (n : ℕ) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeStartedKilledEndpointMeasure n (s+t) (add_pos hs ht) x Ω =
      bridgeProductKilledEndpointMeasure n s t hs ht x Ω := by
  have hE : Measurable (fun f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n)) =>
      x+f ⟨s+t,(add_pos hs ht).le,le_rfl⟩) :=
    measurable_const.add (ContinuousMap.measurable_eval _)
  have hP : Measurable (fun p : C(Icc (0 : ℝ) s, EuclideanSpace ℝ (Fin n)) ×
      C(Icc (0 : ℝ) t, EuclideanSpace ℝ (Fin n)) =>
      x+p.1 ⟨s,hs.le,le_rfl⟩+p.2 ⟨t,ht.le,le_rfl⟩) :=
    (measurable_const.add ((ContinuousMap.measurable_eval _).comp measurable_fst)).add
      ((ContinuousMap.measurable_eval _).comp measurable_snd)
  rw [← bridgeTranslatedKilledEndpointMeasure_eq_started n (s+t) (add_pos hs ht) x Ω hΩ]
  apply Measure.ext
  intro S hS
  rw [bridgeTranslatedKilledEndpointMeasure, Measure.map_apply hE hS,
    Measure.restrict_apply (hS.preimage hE), bridgeProductKilledEndpointMeasure,
    Measure.map_apply hP hS, Measure.restrict_apply (hS.preimage hP),
    ← (bridgeBrownian_split_hasLaw n s t hs ht).map_eq,
    Measure.map_apply (bridgePathSplit_measurable n s t hs.le ht.le)
      ((hS.preimage hP).inter (bridgeComposedSurvivalSet_measurable n s t hs.le x Ω hΩ))]
  congr 1
  ext f
  change (x+f ⟨s+t,(add_pos hs ht).le,le_rfl⟩ ∈ S ∧
      f ∈ bridgeTranslatedSurvivalSet n (s+t) x Ω) ↔
    (x+(bridgePathSplit n s t hs.le ht.le f).1 ⟨s,hs.le,le_rfl⟩ +
      (bridgePathSplit n s t hs.le ht.le f).2 ⟨t,ht.le,le_rfl⟩ ∈ S ∧
      bridgePathSplit n s t hs.le ht.le f ∈ bridgeComposedSurvivalSet n s t hs.le x Ω)
  rw [bridge_survival_split_iff n s t hs.le ht.le x Ω f]
  have he : x+(bridgePathSplit n s t hs.le ht.le f).1 ⟨s,hs.le,le_rfl⟩ +
      (bridgePathSplit n s t hs.le ht.le f).2 ⟨t,ht.le,le_rfl⟩ =
      x+f ⟨s+t,(add_pos hs ht).le,le_rfl⟩ := by
    rw [add_assoc, bridgePathSplit_terminal]
  rw [he]

end AffineFKProof
