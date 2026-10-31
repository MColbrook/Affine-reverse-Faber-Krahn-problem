module

public import AffineFK.ConditionalSteinPairing
public import AffineFK.SteinSumVariance

/-!
# A conditional vector field and its pairings on the image law

One field is chosen before all test functions. Doob--Dynkin factorization
gives its pointwise conditional representation; conditional Jensen bounds
its actual second moment. The bilinear pull-out theorem preserves every
square-integrable strongly measurable vector test.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem scaled_conditional_vector_field
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (A : Ω → EuclideanSpace ℝ (Fin n)) (hA : MemLp A 2 μ)
    (W : Ω → EuclideanSpace ℝ (Fin n)) (hW : Measurable W) (c : ℝ) :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧ MemLp r 2 (μ.map W) ∧
      (∀ ω, r (W ω) = c • condExp
        ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W) μ A ω) ∧
      (∫ x, ‖r x‖ ^ 2 ∂μ.map W) ≤ c ^ 2 * (∫ ω, ‖A ω‖ ^ 2 ∂μ) ∧
      ∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        StronglyMeasurable F → MemLp F 2 (μ.map W) →
        Integrable (fun x => ⟪r x, F x⟫) (μ.map W) ∧
        Integrable (fun ω => ⟪A ω, F (W ω)⟫) μ ∧
        (∫ x, ⟪r x, F x⟫ ∂μ.map W) = c * (∫ ω, ⟪A ω, F (W ω)⟫ ∂μ) := by
  obtain ⟨q, hq, hqLp, hqrep⟩ := conditional_expectation_factor μ A hA W hW
  let r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => c • q x
  have hr : StronglyMeasurable r := hq.const_smul c
  have hrLp : MemLp r 2 (μ.map W) := hqLp.const_smul c
  let s := (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W
  let : MeasurableSpace Ω := mΩ
  have hrep (ω : Ω) : r (W ω) = c • condExp s μ A ω := by
    exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => c • v) (hqrep ω)
  refine ⟨r, hr, hrLp, hrep, ?_, ?_⟩
  · calc
      _ = ∫ ω, ‖r (W ω)‖ ^ 2 ∂μ := integral_map hW.aemeasurable (hr.norm.pow 2).aestronglyMeasurable
      _ = ∫ ω, ‖c • condExp s μ A ω‖ ^ 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => congrArg (fun v => ‖v‖ ^ 2) (hrep ω))
      _ = c ^ 2 * (∫ ω, ‖condExp s μ A ω‖ ^ 2 ∂μ) := by
        simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        exact integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (conditional_second_moment_le μ s hW.comap_le A hA) (sq_nonneg c)
  · intro F hF hFLp
    let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
    have hFW : MemLp (fun ω => F (W ω)) 2 μ :=
      (hasLaw_map hW.aemeasurable).memLp_fun_comp hFLp
    have hprod : Integrable (fun ω => ⟪A ω, F (W ω)⟫) μ :=
      memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hA hFW)
    have hrprod : Integrable (fun x => ⟪r x, F x⟫) (μ.map W) :=
      memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hrLp hFLp)
    have hWs : @Measurable Ω (EuclideanSpace ℝ (Fin n)) s inferInstance W :=
      measurable_iff_comap_le.mpr le_rfl
    have hFs : AEStronglyMeasurable[s] (fun ω => F (W ω)) μ :=
      (hF.comp_measurable hWs).aestronglyMeasurable
    have hp := conditional_bilinear_pairing μ s hW.comap_le B A (hA.integrable (by norm_num))
      (fun ω => F (W ω)) hFs hprod
    change Integrable (fun ω => ⟪condExp s μ A ω, F (W ω)⟫) μ ∧
      (∫ ω, ⟪condExp s μ A ω, F (W ω)⟫ ∂μ) = ∫ ω, ⟪A ω, F (W ω)⟫ ∂μ at hp
    refine ⟨hrprod, hprod, ?_⟩
    calc
      _ = ∫ ω, ⟪r (W ω), F (W ω)⟫ ∂μ :=
        integral_map hW.aemeasurable (hr.inner hF).aestronglyMeasurable
      _ = ∫ ω, c * ⟪condExp s μ A ω, F (W ω)⟫ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          change ⟪r (W ω), F (W ω)⟫ = c * ⟪condExp s μ A ω, F (W ω)⟫
          rw [hrep, real_inner_smul_left]
      _ = c * (∫ ω, ⟪condExp s μ A ω, F (W ω)⟫ ∂μ) := integral_const_mul _ _
      _ = _ := congrArg (fun z : ℝ => c * z) hp.2

end AffineFKProof
