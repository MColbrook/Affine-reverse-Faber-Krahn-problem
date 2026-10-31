module

public import AffineFK.FirstOrderSmoothing
public import AffineFK.ConditionalVectorField

/-!
# The first-order conditional field on the genuine smoothed law

One field is selected before every compact smooth vector test. Its
pointwise conditional representation uses the actual chosen Mathlib
conditional expectation given the affine smoothing map, and its energy
contracts by a². This is a weak-field result; no logarithmic-score or
Fisher-information identification is assumed or asserted here.

Doob--Dynkin, conditional Jensen and bilinear pull-out are reused through
scaled_conditional_vector_field, with the primary Mathlib attributions
retained in that development. Product marginal integration is from
Mathlib.MeasureTheory.Integral.Prod (Floris van Doorn, Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem firstOrder_smoothed_conditional_vector_field
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪s x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧
      MemLp r 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        r (a • p.1 + b • p.2) = a • condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • q.1 + b • q.2))
          (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) (fun q => s q.1) p) ∧
      (∫ x, ‖r x‖ ^ 2 ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ≤ a ^ 2 * (∫ u, ‖s u‖ ^ 2 ∂ν) ∧
      ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
        Integrable (fun x => ⟪r x, F x⟫)
          ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) ∧
        Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x)
          ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) ∧
        (∫ x, ⟪r x, F x⟫ ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) =
          ∫ x, ⟪x, F x⟫ - vectorDivergence n F x
            ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
              (fun p => a • p.1 + b • p.2) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let μ := ν.prod γ
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Measurable W := by fun_prop
  have hA : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => s p.1) 2 μ :=
    hs.comp_fst γ
  obtain ⟨r, hr, hrLp, hrep, hbound, hpair⟩ :=
    scaled_conditional_vector_field μ n (fun p => s p.1) hA W hW a
  have hmarginal :
      (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), ‖s p.1‖ ^ 2 ∂μ) =
        ∫ u, ‖s u‖ ^ 2 ∂ν := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := ν) (ν := γ) (fun u => ‖s u‖ ^ 2))
  refine ⟨r, hr, hrLp, hrep, ?_, ?_⟩
  · simpa only [hmarginal] using hbound
  · intro F
    have hFLp : MemLp F 2 (μ.map W) :=
      (Lp.memLp (testFunctionToL2 (μ.map W) F)).ae_eq (testFunctionToL2_coe (μ.map W) F)
    have hp := hpair F F.continuous.stronglyMeasurable hFLp
    have hraw := firstOrder_smoothed_vector_identity n ν hxi s hs hweak a b ha hb hab F
    have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, F x⟫ - vectorDivergence n F x) := by
      unfold vectorDivergence
      fun_prop
    have hl : Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) (μ.map W) :=
      (integrable_map_measure hc.aestronglyMeasurable hW.aemeasurable).mpr hraw.1
    refine ⟨hp.1, hl, ?_⟩
    calc
      _ = a * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ⟪s p.1, F (W p)⟫ ∂μ) := hp.2.2
      _ = ∫ p, ⟪W p, F (W p)⟫ - vectorDivergence n F (W p) ∂μ := hraw.2.2.symm
      _ = _ := (integral_map hW.aemeasurable hc.aestronglyMeasurable).symm

end AffineFKProof
