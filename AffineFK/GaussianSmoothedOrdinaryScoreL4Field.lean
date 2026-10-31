module

public import AffineFK.GaussianConditionalFieldL4
public import AffineFK.GaussianSmoothingProduct
public import AffineFK.VectorTestUniqueness

/-!
# The ordinary Gaussian conditional score field

One original image-law field is chosen as -b^{-1} E[G | aU+bG]. The same
field has L2 and L4 membership. Gaussian product integration by parts
proves its compact ordinary weak-score identity without any moment or
density condition on the first probability law. Logarithmic-score
identification is a separate theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem gaussianSmoothing_ordinary_score_field (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧
      MemLp r 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      MemLp r 4 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      Integrable (fun x => ‖r x‖ ^ 4) ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        r (a • p.1 + b • p.2) = (-b⁻¹) • condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • q.1 + b • q.2))
          (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) Prod.snd p) ∧
      (∫ x, ‖r x‖ ^ 4 ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ≤ (b⁻¹) ^ 4 * ((n : ℝ) * (n + 2)) ∧
      ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
        Integrable (fun x => r x i * φ x) ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) ∧
        Integrable (partialTest n i φ) ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) ∧
        (∫ x, r x i * φ x ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) =
            -(∫ x, partialTest n i φ x ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
              (fun p => a • p.1 + b • p.2)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let μ := ν.prod γ
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Measurable W := by fun_prop
  let : IsProbabilityMeasure (μ.map W) := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hq : MemLp (Prod.snd : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n)) 2 μ := (IsGaussian.memLp_id γ 2 (by norm_num)).comp_snd ν
  obtain ⟨r, hr, hr2, hrep, _hbound2, hpair⟩ :=
    scaled_conditional_vector_field μ n Prod.snd hq W hW (-b⁻¹)
  have hfour := gaussian_conditional_vector_field_memLp_four n ν a b (-b⁻¹) r hr hrep
  have hnegative : (-b⁻¹) ^ 4 = (b⁻¹) ^ 4 := by ring
  have hbound := hfour.2.2
  rw [hnegative] at hbound
  refine ⟨r, hr, hr2, hfour.1, hfour.2.1, hrep, hbound, ?_⟩
  intro i φ
  let F := singleComponentTest n i φ
  have hF : MemLp F 2 (μ.map W) :=
    (Lp.memLp (testFunctionToL2 (μ.map W) F)).ae_eq (testFunctionToL2_coe (μ.map W) F)
  have hp := hpair F F.continuous.stronglyMeasurable hF
  dsimp only [F] at hp
  simp_rw [singleComponentTest_inner_at] at hp
  have hG := product_gaussian_smoothing_integration_by_parts n ν i a b hb.ne' φ
  have hd : Integrable (partialTest n i φ) (μ.map W) :=
    (testFunction_memLp_two n (μ.map W) (partialTest n i φ)).integrable (by norm_num)
  refine ⟨hp.1, hd, ?_⟩
  calc
    _ = (-b⁻¹) * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        p.2 i * φ (W p) ∂μ) := hp.2.2
    _ = (-b⁻¹) * (b * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i φ (W p) ∂μ)) := by rw [hG.2.2]
    _ = -(∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i φ (W p) ∂μ) := by
      rw [← mul_assoc, neg_mul, inv_mul_cancel₀ hb.ne', neg_one_mul]
    _ = _ := by
      congr 1
      exact (integral_map hW.aemeasurable
        (partialTest n i φ).continuous.aestronglyMeasurable).symm

end AffineFKProof
