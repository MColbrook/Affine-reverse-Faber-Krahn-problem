module

public import AffineFK.OrdinaryFisherConvolutionScore
public import AffineFK.AffineProductIntegrability
public import AffineFK.ConditionalVectorField

/-!
# Ordinary weak scores under convolution with an arbitrary probability law

Only the second summand has a weak ordinary score. The first law is any
probability measure; no density or moment assumption is imposed on it.
Translated compact smooth tests justify the distributional equation, and
all product integrals are proved integrable before Fubini. One output field
is chosen by the actual conditional expectation before every vector test.

This module proves weak-score and energy inheritance. The converse from a
weak score to square-root-density H1 membership is a separate assertion;
the output here is not labelled the full Sobolev Fisher inequality.

Fubini and product marginal integration reuse Mathlib.MeasureTheory.Integral.Prod
(Floris van Doorn, Apache-2.0). Conditional expectation, Doob--Dynkin and
conditional Jensen are reused through ConditionalVectorField.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem ordinaryFisher_convolution_component_identity
    (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 η)
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ y, s y i * φ y ∂η) = -(∫ y, partialTest n i φ y ∂η))
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      s p.2 i * φ (p.1 + p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (p.1 + p.2)) (ν.prod η) ∧
    (∫ p, s p.2 i * φ (p.1 + p.2) ∂ν.prod η) =
      -(∫ p, partialTest n i φ (p.1 + p.2) ∂ν.prod η) := by
  have hsum : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      p.1 + p.2) := by fun_prop
  have hleft := integrable_snd_mul_test_comp n ν η (fun y => s y i)
    ((hs.eval_piLp i).integrable (by norm_num)) _ hsum φ
  have hright : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        partialTest n i φ (p.1 + p.2)) (ν.prod η) := by
    simpa only [one_mul] using integrable_snd_mul_test_comp n ν η (fun _ => (1 : ℝ))
      (integrable_const 1) _ hsum (partialTest n i φ)
  refine ⟨hleft, hright, ?_⟩
  rw [integral_prod _ hleft, integral_prod _ hright, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have h := hweak i (translatedTestFunction x φ)
    simpa only [partialTest_translated, translatedTestFunction_apply, add_comm] using h

theorem ordinaryFisher_convolution_vector_identity
    (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 η)
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ y, s y i * φ y ∂η) = -(∫ y, partialTest n i φ y ∂η))
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n))) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪s p.2, F (p.1 + p.2)⟫) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      vectorDivergence n F (p.1 + p.2)) (ν.prod η) ∧
    (∫ p, ⟪s p.2, F (p.1 + p.2)⟫ ∂ν.prod η) =
      -(∫ p, vectorDivergence n F (p.1 + p.2) ∂ν.prod η) := by
  have hc (i : Fin n) := ordinaryFisher_convolution_component_identity n ν η s hs hweak i
    (vectorComponentTest n i F)
  have hleft : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ⟪s p.2, F (p.1 + p.2)⟫) =
      (fun p => ∑ i : Fin n, s p.2 i * vectorComponentTest n i F (p.1 + p.2)) := by
    funext p
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      vectorComponentTest_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hright : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      vectorDivergence n F (p.1 + p.2)) =
      (fun p => ∑ i : Fin n, partialTest n i (vectorComponentTest n i F) (p.1 + p.2)) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact integrable_finsetSum _ fun i _ => (hc i).1
  · rw [hright]
    exact integrable_finsetSum _ fun i _ => (hc i).2.1
  · rw [hleft, hright, integral_finsetSum _ fun i _ => (hc i).1,
      integral_finsetSum _ fun i _ => (hc i).2.1, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => (hc i).2.2

theorem ordinaryFisher_convolution_conditional_score
    (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 η)
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ y, s y i * φ y ∂η) = -(∫ y, partialTest n i φ y ∂η)) :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧ MemLp r 2 ((ν.prod η).map (fun p => p.1 + p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        r (p.1 + p.2) = condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => q.1 + q.2))
          (ν.prod η) (fun q => s q.2) p) ∧
      (∫ x, ‖r x‖ ^ 2 ∂(ν.prod η).map (fun p => p.1 + p.2)) ≤
        ∫ y, ‖s y‖ ^ 2 ∂η ∧
      ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
        Integrable (fun x => ⟪r x, F x⟫) ((ν.prod η).map (fun p => p.1 + p.2)) ∧
        Integrable (vectorDivergence n F) ((ν.prod η).map (fun p => p.1 + p.2)) ∧
        (∫ x, ⟪r x, F x⟫ ∂(ν.prod η).map (fun p => p.1 + p.2)) =
          -(∫ x, vectorDivergence n F x ∂(ν.prod η).map (fun p => p.1 + p.2)) := by
  let μ := ν.prod η
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => p.1 + p.2
  have hW : Measurable W := by fun_prop
  have hA : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => s p.2) 2 μ :=
    hs.comp_snd ν
  obtain ⟨r, hr, hrLp, hrep, hbound, hpair⟩ :=
    scaled_conditional_vector_field μ n (fun p => s p.2) hA W hW 1
  have hmarginal : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖s p.2‖ ^ 2 ∂μ) = ∫ y, ‖s y‖ ^ 2 ∂η := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_snd (μ := ν) (ν := η) (fun y => ‖s y‖ ^ 2))
  refine ⟨r, hr, hrLp, ?_, ?_, ?_⟩
  · intro p
    simpa only [one_smul] using hrep p
  · simpa only [one_pow, one_mul, hmarginal] using hbound
  · intro F
    have hFLp : MemLp F 2 (μ.map W) :=
      (Lp.memLp (testFunctionToL2 (μ.map W) F)).ae_eq (testFunctionToL2_coe (μ.map W) F)
    have hp := hpair F F.continuous.stronglyMeasurable hFLp
    have hraw := ordinaryFisher_convolution_vector_identity n ν η s hs hweak F
    have hdiv : Continuous (vectorDivergence n F) := by
      unfold vectorDivergence
      fun_prop
    have hd : Integrable (vectorDivergence n F) (μ.map W) :=
      (integrable_map_measure hdiv.aestronglyMeasurable hW.aemeasurable).mpr hraw.2.1
    refine ⟨hp.1, hd, ?_⟩
    calc
      _ = ∫ p, ⟪s p.2, F (W p)⟫ ∂μ := by simpa only [one_mul] using hp.2.2
      _ = -(∫ p, vectorDivergence n F (W p) ∂μ) := hraw.2.2
      _ = _ := congrArg Neg.neg (integral_map hW.aemeasurable hdiv.aestronglyMeasurable).symm

end AffineFKProof
