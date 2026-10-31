module

public import AffineFK.ConditionalVectorField
public import AffineFK.AffineGaussianIntegrationByParts
public import AffineFK.AffineProductIntegrability
public import AffineFK.SmoothPartials

/-!
# Conditional scalar fields for second Gaussian derivatives

Doob--Dynkin and conditional Jensen choose one scalar field before every
test. The Gaussian quadratic coefficient has its actual square moment;
two Gaussian integrations by parts give the genuine second-test identity.
The conditional and Gaussian ingredients are reused from the attributed
Mathlib-backed project developments, with all L1 premises retained.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem scaled_conditional_scalar_field
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ℝ) (hA : MemLp A 2 μ) (W : Ω → X) (hW : Measurable W) (c : ℝ) :
    ∃ q : X → ℝ, StronglyMeasurable q ∧ MemLp q 2 (μ.map W) ∧
      (∀ ω, q (W ω) = c * condExp (mX.comap W) μ A ω) ∧
      (∫ x, (q x) ^ 2 ∂μ.map W) ≤ c ^ 2 * (∫ ω, (A ω) ^ 2 ∂μ) ∧
      ∀ f : X → ℝ, StronglyMeasurable f → MemLp f 2 (μ.map W) →
        Integrable (fun x => q x * f x) (μ.map W) ∧
        Integrable (fun ω => A ω * f (W ω)) μ ∧
        (∫ x, q x * f x ∂μ.map W) = c * (∫ ω, A ω * f (W ω) ∂μ) := by
  obtain ⟨g, hg, hg2, hgrep⟩ := conditional_expectation_factor μ A hA W hW
  let q : X → ℝ := fun x => c * g x
  have hq : StronglyMeasurable q := hg.const_mul c
  have hq2 : MemLp q 2 (μ.map W) := hg2.const_mul c
  let s := mX.comap W
  let : MeasurableSpace Ω := mΩ
  have hrep (ω : Ω) : q (W ω) = c * condExp s μ A ω :=
    congrArg (fun v : ℝ => c * v) (hgrep ω)
  refine ⟨q, hq, hq2, hrep, ?_, ?_⟩
  · calc
      _ = ∫ ω, (q (W ω)) ^ 2 ∂μ :=
        integral_map hW.aemeasurable (hq.pow 2).aestronglyMeasurable
      _ = ∫ ω, c ^ 2 * (condExp s μ A ω) ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          change (q (W ω)) ^ 2 = c ^ 2 * (condExp s μ A ω) ^ 2
          rw [hrep, mul_pow]
      _ = c ^ 2 * (∫ ω, (condExp s μ A ω) ^ 2 ∂μ) := integral_const_mul _ _
      _ ≤ _ := by
        have h := conditional_second_moment_le μ s hW.comap_le A hA
        simp only [Real.norm_eq_abs, sq_abs] at h
        exact mul_le_mul_of_nonneg_left h (sq_nonneg c)
  · intro f hf hf2
    have hfW : MemLp (fun ω => f (W ω)) 2 μ :=
      (hasLaw_map hW.aemeasurable).memLp_fun_comp hf2
    have hp : Integrable (fun ω => A ω * f (W ω)) μ := hA.integrable_mul hfW
    have hqp : Integrable (fun x => q x * f x) (μ.map W) := hq2.integrable_mul hf2
    have hWs : @Measurable Ω X s mX W := measurable_iff_comap_le.mpr le_rfl
    have hfs : AEStronglyMeasurable[s] (fun ω => f (W ω)) μ :=
      (hf.comp_measurable hWs).aestronglyMeasurable
    have h := conditional_bilinear_pairing μ s hW.comap_le (ContinuousLinearMap.mul ℝ ℝ)
      A (hA.integrable (by norm_num)) (fun ω => f (W ω)) hfs hp
    refine ⟨hqp, hp, ?_⟩
    calc
      _ = ∫ ω, q (W ω) * f (W ω) ∂μ :=
        integral_map hW.aemeasurable (hq.mul hf).aestronglyMeasurable
      _ = ∫ ω, c * (condExp s μ A ω * f (W ω)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          change q (W ω) * f (W ω) = c * (condExp s μ A ω * f (W ω))
          rw [hrep, mul_assoc]
      _ = c * (∫ ω, condExp s μ A ω * f (W ω) ∂μ) := integral_const_mul _ _
      _ = _ := congrArg (fun z : ℝ => c * z) h.2

theorem product_gaussian_second_integration_by_parts
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i j : Fin n) (a b : ℝ) (hb : b ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (p.2 i * p.2 j - if i = j then 1 else 0) * φ (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i (partialTest n j φ) (a • p.1 + b • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      (p.2 i * p.2 j - if i = j then 1 else 0) * φ (a • p.1 + b • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      b ^ 2 * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i (partialTest n j φ) (a • p.1 + b • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Continuous W := by fun_prop
  have hQ := stdGaussian_quadratic_memLp n i j
  have hL := integrable_snd_mul_test_comp n ν γ _ (hQ.integrable (by norm_num)) W hW φ
  have hR : Integrable (fun p => partialTest n i (partialTest n j φ) (W p)) (ν.prod γ) := by
    simpa only [one_mul] using integrable_fst_mul_test_comp n ν γ (fun _ => (1 : ℝ))
      (integrable_const 1) W hW (partialTest n i (partialTest n j φ))
  refine ⟨hL, hR, ?_⟩
  calc
    _ = ∫ u, (∫ g, (g i * g j - if i = j then 1 else 0) * φ (a • u + b • g) ∂γ) ∂ν :=
      integral_prod _ hL
    _ = ∫ u, b ^ 2 * (∫ g, partialTest n i (partialTest n j φ) (a • u + b • g) ∂γ) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        have h := (stdGaussian_affine_second_integration_by_parts n i j b hb (a • u) φ).2.2
        simpa only [add_comm, partialTest_commute n j i φ] using h
    _ = b ^ 2 * (∫ u, (∫ g, partialTest n i (partialTest n j φ) (a • u + b • g) ∂γ) ∂ν) :=
      integral_const_mul _ _
    _ = _ := by rw [← integral_prod _ hR]

end AffineFKProof
