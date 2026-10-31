module

public import AffineFK.BridgeKilledEndpointComposition
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Chapman--Kolmogorov for the actual killed Brownian endpoint measures

This follows from the actual independent continuous-path split and Tonelli
on its genuine product probability. Open-domain survival includes both
endpoints. No semigroup or transition-law identity is supplied as a premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridge_killed_endpoint_apply_eq_section (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (Ω S : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (hS : MeasurableSet S) :
    bridgeStartedKilledEndpointMeasure n T hT x Ω S =
      bridgeScaledBrownianLaw n T hT {f | x+f ⟨T,hT.le,le_rfl⟩ ∈ S ∧
        (∀ r, x+f r ∈ Ω)} := by
  have he : Measurable (fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) =>
      x+f ⟨T,hT.le,le_rfl⟩) := measurable_const.add (ContinuousMap.measurable_eval _)
  rw [← bridgeTranslatedKilledEndpointMeasure_eq_started n T hT x Ω hΩ,
    bridgeTranslatedKilledEndpointMeasure, Measure.map_apply he hS,
    Measure.restrict_apply (hS.preimage he)]
  rfl

theorem bridge_killed_endpoint_apply_measurable (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω S : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) (hS : MeasurableSet S) :
    Measurable (fun x => bridgeStartedKilledEndpointMeasure n T hT x Ω S) := by
  let A : Set (EuclideanSpace ℝ (Fin n) × C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n))) :=
    {p | p.1+p.2 ⟨T,hT.le,le_rfl⟩ ∈ S ∧ ∀ r, p.1+p.2 r ∈ Ω}
  have hA : MeasurableSet A :=
    ((hS.preimage (ContinuousMap.measurable_eval _)).inter
      (bridgeFiniteSurvivalSet_isOpen n T Ω hΩ).measurableSet).preimage
        (bridgeTranslatePath_joint_measurable n T)
  have h := measurable_measure_prodMk_left (ν := bridgeScaledBrownianLaw n T hT) hA
  convert h using 1
  funext x
  exact bridge_killed_endpoint_apply_eq_section n T hT x Ω S hΩ hS

theorem bridge_killed_chapman_kolmogorov (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω S : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (hS : MeasurableSet S) :
    bridgeStartedKilledEndpointMeasure n (s+t) (add_pos hs ht) x Ω S =
      ∫⁻ y, bridgeStartedKilledEndpointMeasure n t ht y Ω S
        ∂bridgeStartedKilledEndpointMeasure n s hs x Ω := by
  classical
  let μ := bridgeScaledBrownianLaw n s hs
  let ν := bridgeScaledBrownianLaw n t ht
  let K := fun y => bridgeStartedKilledEndpointMeasure n t ht y Ω S
  let E := fun f : C(Icc (0 : ℝ) s, EuclideanSpace ℝ (Fin n)) => x+f ⟨s,hs.le,le_rfl⟩
  let P := fun p : C(Icc (0 : ℝ) s, EuclideanSpace ℝ (Fin n)) ×
      C(Icc (0 : ℝ) t, EuclideanSpace ℝ (Fin n)) =>
      x+p.1 ⟨s,hs.le,le_rfl⟩+p.2 ⟨t,ht.le,le_rfl⟩
  let D := bridgeTranslatedSurvivalSet n s x Ω
  let A := P ⁻¹' S ∩ bridgeComposedSurvivalSet n s t hs.le x Ω
  have hE : Measurable E := measurable_const.add (ContinuousMap.measurable_eval _)
  have hP : Measurable P :=
    (measurable_const.add ((ContinuousMap.measurable_eval _).comp measurable_fst)).add
      ((ContinuousMap.measurable_eval _).comp measurable_snd)
  have hK : Measurable K := bridge_killed_endpoint_apply_measurable n t ht Ω S hΩ hS
  have hD : MeasurableSet D := bridgeTranslatedSurvivalSet_measurable n s x Ω hΩ
  have hA : MeasurableSet A :=
    (hS.preimage hP).inter (bridgeComposedSurvivalSet_measurable n s t hs.le x Ω hΩ)
  calc
    bridgeStartedKilledEndpointMeasure n (s+t) (add_pos hs ht) x Ω S = (μ.prod ν) A := by
      rw [bridgeStartedKilledEndpointMeasure_eq_product n s t hs ht x Ω hΩ,
        bridgeProductKilledEndpointMeasure, Measure.map_apply hP hS,
        Measure.restrict_apply (hS.preimage hP)]
    _ = ∫⁻ f, ν (Prod.mk f ⁻¹' A) ∂μ := Measure.prod_apply hA
    _ = ∫⁻ f, D.indicator (fun f => K (E f)) f ∂μ := by
      apply lintegral_congr
      intro f
      by_cases hf : f ∈ D
      · rw [Set.indicator_of_mem hf]
        dsimp [K, E]
        rw [bridge_killed_endpoint_apply_eq_section n t ht _ Ω S hΩ hS]
        congr 1
        ext g
        have hf' : ∀ r, x+f r ∈ Ω := hf
        change ((x+f ⟨s,hs.le,le_rfl⟩+g ⟨t,ht.le,le_rfl⟩ ∈ S) ∧
          (∀ r, x+f r ∈ Ω) ∧ ∀ u, x+f ⟨s,hs.le,le_rfl⟩+g u ∈ Ω) ↔ _
        constructor
        · rintro ⟨he,_,hg⟩
          exact ⟨he,hg⟩
        · rintro ⟨he,hg⟩
          exact ⟨he,hf',hg⟩
      · rw [Set.indicator_of_notMem hf]
        have hzero : Prod.mk f ⁻¹' A = ∅ := by
          ext g
          have hf' : ¬ ∀ r, x+f r ∈ Ω := hf
          change ((x+f ⟨s,hs.le,le_rfl⟩+g ⟨t,ht.le,le_rfl⟩ ∈ S) ∧
            (∀ r, x+f r ∈ Ω) ∧ ∀ u, x+f ⟨s,hs.le,le_rfl⟩+g u ∈ Ω) ↔ False
          constructor
          · intro h
            exact hf' h.2.1
          · exact False.elim
        rw [hzero, measure_empty]
    _ = ∫⁻ f, K (E f) ∂μ.restrict D := lintegral_indicator hD _
    _ = ∫⁻ y, K y ∂bridgeTranslatedKilledEndpointMeasure n s hs x Ω :=
      (lintegral_map hK hE).symm
    _ = ∫⁻ y, K y ∂bridgeStartedKilledEndpointMeasure n s hs x Ω := by
      rw [bridgeTranslatedKilledEndpointMeasure_eq_started n s hs x Ω hΩ]

end AffineFKProof
