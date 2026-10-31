module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Continuous-path laws are determined by finite-dimensional laws

The proof uses the actual Borel sigma algebra of the compact-open
continuous-path space and uniqueness of finite projective limits.
Reuse: the continuous-map Borel theorem and the projective-limit uniqueness
proof by Mathlib contributors, Rémy Degenne and Peter Pfaffelhuber.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set

theorem bridge_measure_eq_of_comap_map_eq {Ω Λ : Type*} [mΩ : MeasurableSpace Ω]
    [mΛ : MeasurableSpace Λ] (F : Ω → Λ) (hF : Measurable F)
    (hm : mΩ = mΛ.comap F) (μ ν : Measure Ω) (h : μ.map F = ν.map F) : μ = ν := by
  apply Measure.ext
  intro S hS
  rw [hm] at hS
  obtain ⟨A, hA, rfl⟩ := hS
  rw [← Measure.map_apply hF hA, ← Measure.map_apply hF hA, h]

theorem bridge_continuousMap_measurableSpace_eq_comap_eval {X E : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace E] [SecondCountableTopology E] [RegularSpace E]
    [MeasurableSpace E] [BorelSpace E] :
    (inferInstance : MeasurableSpace C(X, E)) =
      (inferInstance : MeasurableSpace (X → E)).comap (fun f : C(X, E) => fun t => f t) := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def]

theorem bridge_continuous_path_law_ext {X E : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace E] [SecondCountableTopology E] [RegularSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure C(X, E)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : ∀ I : Finset X,
      μ.map (fun f : C(X, E) => I.restrict (fun t => f t)) =
        ν.map (fun f : C(X, E) => I.restrict (fun t => f t))) : μ = ν := by
  let F : C(X, E) → X → E := fun f t => f t
  have hF : Measurable F := Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)
  apply bridge_measure_eq_of_comap_map_eq F hF bridge_continuousMap_measurableSpace_eq_comap_eval μ ν
  let P : (I : Finset X) → Measure (I → E) := fun I => μ.map (fun f => I.restrict (fun t => f t))
  letI (I : Finset X) : IsFiniteMeasure (P I) := by dsimp [P]; infer_instance
  apply IsProjectiveLimit.unique (P := P)
  · intro I
    exact Measure.map_map (Measurable.of_eval (fun (i : I) => measurable_pi_apply i.1)) hF
  · intro I
    have hr : Measurable (I.restrict : (X → E) → I → E) :=
      Measurable.of_eval (fun (i : I) => measurable_pi_apply i.1)
    rw [Measure.map_map hr hF]
    exact (hfinite I).symm

end AffineFKProof
