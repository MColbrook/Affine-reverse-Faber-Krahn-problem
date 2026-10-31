module

public import AffineFK.SmoothedSteinVector
public import AffineFK.GaussianHermiteConditionalField

/-!
# A square-integrable vector field for the smoothed Stein identity

The same field has the conditional Gaussian representation, the exact
energy bound, and every compact smooth vector test identity on the actual
smoothed law. Identification with a logarithmic derivative is separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem smoothed_stein_vector_field
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) = ∫ x, vectorHessianContraction n T F x ∂ν)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧
      MemLp r 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        r (a • p.1 + b • p.2) = (a ^ 3 / b ^ 2) • condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • q.1 + b • q.2))
          (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
          (fun q => gaussianHermiteContraction n (T q.1) q.2) p) ∧
      (∫ x, ‖r x‖ ^ 2 ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ≤
        (2 * a ^ 6 / b ^ 4) * (∫ u, ‖T u‖ ^ 2 ∂ν) ∧
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
  let μ := ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Measurable W := by fun_prop
  obtain ⟨r, hr, hrLp, hrep, hbound, hpair⟩ := gaussian_hermite_conditional_field n ν T hT a b (a ^ 3 / b ^ 2)
  refine ⟨r, hr, hrLp, hrep, ?_, ?_⟩
  · convert hbound using 1 <;> ring
  · intro F
    have hFLp : MemLp F 2 (μ.map W) :=
      (Lp.memLp (testFunctionToL2 (μ.map W) F)).ae_eq (testFunctionToL2_coe (μ.map W) F)
    have hp := hpair F F.continuous.stronglyMeasurable hFLp
    have hs := smoothed_stein_vector_identities n ν hxi T hT hidentity a b ha hb hab F
    have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, F x⟫ - vectorDivergence n F x) := by
      unfold vectorDivergence
      fun_prop
    have hl : Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) (μ.map W) :=
      (integrable_map_measure hc.aestronglyMeasurable hW.aemeasurable).mpr hs.1
    refine ⟨hp.1, hl, ?_⟩
    calc
      _ = (a ^ 3 / b ^ 2) * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ⟪gaussianHermiteContraction n (T p.1) p.2, F (W p)⟫ ∂μ) := hp.2.2
      _ = ∫ p, ⟪W p, F (W p)⟫ - vectorDivergence n F (W p) ∂μ := hs.2.2.2.2.symm
      _ = _ := (integral_map hW.aemeasurable hc.aestronglyMeasurable).symm

end AffineFKProof
