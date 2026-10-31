module

public import AffineFK.SteinTensorAssembly
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.HasLaw

/-!
# Conditional expectation paired with tests of the conditioning variable

Mathlib's bilinear pull-out theorem, due to Etienne Marion, Remy Degenne
and Kexing Ying, preserves the actual integral against a coarsely measurable
test. The tensor-coordinate consequence below includes the integrability
guards and the actual scaled representation, rather than assuming its pairing.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem conditional_bilinear_pairing
    {Ω E F : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : MeasurableSpace Ω) (hs : s ≤ mΩ)
    (B : E →L[ℝ] F →L[ℝ] ℝ) (A : Ω → E) (hA : Integrable A μ)
    (g : Ω → F) (hg : AEStronglyMeasurable[s] g μ)
    (hprod : Integrable (fun ω => B (A ω) (g ω)) μ) :
    Integrable (fun ω => B (condExp s μ A ω) (g ω)) μ ∧
      (∫ ω, B (condExp s μ A ω) (g ω) ∂μ) = ∫ ω, B (A ω) (g ω) ∂μ := by
  let : MeasurableSpace Ω := mΩ
  have h := condExp_bilin_of_aestronglyMeasurable_right B hg hprod hA
  refine ⟨integrable_condExp.congr h, ?_⟩
  calc
    _ = ∫ ω, condExp s μ (fun x => B (A x) (g x)) ω ∂μ := integral_congr_ae h.symm
    _ = _ := integral_condExp hs

theorem conditional_tensor_coordinate_pairing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : MeasurableSpace Ω) (hs : s ≤ mΩ)
    (n : ℕ) (A : Ω → EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (hA : Integrable A μ)
    (g : Ω → ℝ) (hg : AEStronglyMeasurable[s] g μ) (p : Fin n × Fin n × Fin n)
    (hprod : Integrable (fun ω => A ω p * g ω) μ) :
    Integrable (fun ω => (condExp s μ A ω) p * g ω) μ ∧
      (∫ ω, (condExp s μ A ω) p * g ω ∂μ) = ∫ ω, A ω p * g ω ∂μ := by
  let : MeasurableSpace Ω := mΩ
  let B : EuclideanSpace ℝ (Fin n × Fin n × Fin n) →L[ℝ] ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).comp
      (innerSL ℝ (EuclideanSpace.basisFun (Fin n × Fin n × Fin n) ℝ p))
  have hB (v : EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (c : ℝ) : B v c = v p * c := by
    change ⟪EuclideanSpace.basisFun (Fin n × Fin n × Fin n) ℝ p, v⟫ * c = _
    rw [EuclideanSpace.basisFun_inner]
  have hp : Integrable (fun ω => B (A ω) (g ω)) μ := by
    simpa only [hB] using hprod
  simpa only [hB] using conditional_bilinear_pairing μ s hs B A hA g hg hp

theorem tensor_coordinate_test_pairing_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (W : Ω → EuclideanSpace ℝ (Fin n)) (hW : Measurable W)
    (A : Ω → EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (hA : MemLp A 2 μ)
    (p : Fin n × Fin n × Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun ω => A ω p * φ (W ω)) μ := by
  have hφ : MemLp φ 2 (μ.map W) :=
    (Lp.memLp (testFunctionToL2 (μ.map W) φ)).ae_eq (testFunctionToL2_coe (μ.map W) φ)
  have hψ : MemLp (fun ω => φ (W ω)) 2 μ := (hasLaw_map hW.aemeasurable).memLp_fun_comp hφ
  exact (hA.eval_piLp p).integrable_mul hψ

theorem conditional_tensor_representation_pairing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (W : Ω → EuclideanSpace ℝ (Fin n)) (hW : Measurable W)
    (A : Ω → EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (hA : MemLp A 2 μ)
    (Tm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (c : ℝ)
    (hrep : ∀ ω, Tm (W ω) = c •
      condExp ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W) μ A ω)
    (p : Fin n × Fin n × Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun ω => Tm (W ω) p * φ (W ω)) μ ∧
      (∫ ω, Tm (W ω) p * φ (W ω) ∂μ) = c * ∫ ω, A ω p * φ (W ω) ∂μ := by
  let s := (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W
  let : MeasurableSpace Ω := mΩ
  have hWs : @Measurable Ω (EuclideanSpace ℝ (Fin n)) s inferInstance W :=
    measurable_iff_comap_le.mpr le_rfl
  have hφ : AEStronglyMeasurable[s] (fun ω => φ (W ω)) μ :=
    (φ.continuous.stronglyMeasurable.comp_measurable hWs).aestronglyMeasurable
  have h := conditional_tensor_coordinate_pairing μ s hW.comap_le n A
    (hA.integrable (by norm_num)) (fun ω => φ (W ω)) hφ p
    (tensor_coordinate_test_pairing_integrable μ n W hW A hA p φ)
  have hpoint (ω : Ω) : Tm (W ω) p * φ (W ω) = c * ((condExp s μ A ω) p * φ (W ω)) := by
    rw [hrep]
    change (c * (condExp s μ A ω) p) * φ (W ω) = _
    ring
  refine ⟨(h.1.const_mul c).congr (Filter.Eventually.of_forall fun ω => (hpoint ω).symm), ?_⟩
  calc
    _ = ∫ ω, c * ((condExp s μ A ω) p * φ (W ω)) ∂μ := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = c * (∫ ω, (condExp s μ A ω) p * φ (W ω) ∂μ) := integral_const_mul _ _
    _ = _ := congrArg (fun x : ℝ => c * x) h.2

end AffineFKProof
