module

public import AffineFK.ConditionalVectorField
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Tactic.Positivity

/-!
# Fourth moments of a chosen conditional vector field

The field on the actual image law is kept fixed. Its pointwise conditional
representation and genuine input L4 membership imply output L4 membership
and the actual fourth-moment bound. The final construction retains the
earlier single field, its L2 estimate and every L2 test pairing.

Conditional Lp and integral contraction reuse Mathlib's proofs by Remy
Degenne, Kexing Ying and contributors (Apache-2.0). No contraction or
output integrability is an assumption.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem conditional_fourth_moment_le
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : MeasurableSpace Ω) (_hs : s ≤ mΩ)
    (q : Ω → E) (hq : MemLp q 4 μ) :
    MemLp (condExp s μ q) 4 μ ∧
    Integrable (fun ω => ‖condExp s μ q ω‖ ^ 4) μ ∧
    (∫ ω, ‖condExp s μ q ω‖ ^ 4 ∂μ) ≤ ∫ ω, ‖q ω‖ ^ 4 ∂μ := by
  let : MeasurableSpace Ω := mΩ
  have hce : MemLp (condExp s μ q) 4 μ := hq.condExp (by norm_num)
  have hq4 : Integrable (fun ω => ‖q ω‖ ^ 4) μ := hq.integrable_norm_pow (by norm_num)
  have hpow (v : E) : ‖v‖ ^ (4 : ℝ) = ‖v‖ ^ (4 : ℕ) := Real.rpow_natCast ‖v‖ 4
  refine ⟨hce, hce.integrable_norm_pow (by norm_num), ?_⟩
  simpa only [hpow] using
    (integral_norm_condExp_rpow_le (m := s) (μ := μ) (f := q) (p := (4 : ℝ))
      (by norm_num) (by simpa only [hpow] using hq4))

theorem conditional_vector_field_memLp_four
    {Ω X E : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → E) (hq : MemLp q 4 μ) (W : Ω → X) (hW : Measurable W) (c : ℝ)
    (g : X → E) (hg : StronglyMeasurable g)
    (hrep : ∀ ω, g (W ω) = c • condExp (mX.comap W) μ q ω) :
    MemLp g 4 (μ.map W) ∧
    Integrable (fun x => ‖g x‖ ^ 4) (μ.map W) ∧
    Integrable (fun ω => ‖q ω‖ ^ 4) μ ∧
    (∫ x, ‖g x‖ ^ 4 ∂μ.map W) ≤ c ^ 4 * (∫ ω, ‖q ω‖ ^ 4 ∂μ) := by
  let s := mX.comap W
  let : MeasurableSpace Ω := mΩ
  have hce := conditional_fourth_moment_le μ s hW.comap_le q hq
  have hcomp : MemLp (fun ω => g (W ω)) 4 μ :=
    (hce.1.const_smul c).ae_eq (Filter.Eventually.of_forall fun ω => (hrep ω).symm)
  have hg4 : MemLp g 4 (μ.map W) :=
    (memLp_map_measure_iff hg.aestronglyMeasurable hW.aemeasurable).mpr hcomp
  refine ⟨hg4, hg4.integrable_norm_pow (by norm_num), hq.integrable_norm_pow (by norm_num), ?_⟩
  have hc : ‖c‖ ^ 4 = c ^ 4 := by
    calc
      _ = (‖c‖ ^ 2) ^ 2 := by ring
      _ = (c ^ 2) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      _ = _ := by ring
  calc
    _ = ∫ ω, ‖g (W ω)‖ ^ 4 ∂μ :=
      integral_map hW.aemeasurable (hg.norm.pow 4).aestronglyMeasurable
    _ = ∫ ω, ‖c • condExp s μ q ω‖ ^ 4 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => congrArg (fun v => ‖v‖ ^ 4) (hrep ω))
    _ = c ^ 4 * (∫ ω, ‖condExp s μ q ω‖ ^ 4 ∂μ) := by
      simp_rw [norm_smul, mul_pow, hc]
      exact integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hce.2.2 (by positivity)

theorem scaled_conditional_vector_field_fourth_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (q : Ω → EuclideanSpace ℝ (Fin n)) (hq : MemLp q 4 μ)
    (W : Ω → EuclideanSpace ℝ (Fin n)) (hW : Measurable W) (c : ℝ) :
    ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable g ∧ MemLp g 2 (μ.map W) ∧ MemLp g 4 (μ.map W) ∧
      Integrable (fun x => ‖g x‖ ^ 4) (μ.map W) ∧
      (∀ ω, g (W ω) = c • condExp
        ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W) μ q ω) ∧
      (∫ x, ‖g x‖ ^ 2 ∂μ.map W) ≤ c ^ 2 * (∫ ω, ‖q ω‖ ^ 2 ∂μ) ∧
      (∫ x, ‖g x‖ ^ 4 ∂μ.map W) ≤ c ^ 4 * (∫ ω, ‖q ω‖ ^ 4 ∂μ) ∧
      ∀ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        StronglyMeasurable F → MemLp F 2 (μ.map W) →
        Integrable (fun x => ⟪g x, F x⟫) (μ.map W) ∧
        Integrable (fun ω => ⟪q ω, F (W ω)⟫) μ ∧
        (∫ x, ⟪g x, F x⟫ ∂μ.map W) = c * (∫ ω, ⟪q ω, F (W ω)⟫ ∂μ) := by
  have hq2 : MemLp q 2 μ := hq.mono_exponent (by norm_num)
  obtain ⟨g, hg, hg2, hrep, hbound2, hpair⟩ := scaled_conditional_vector_field μ n q hq2 W hW c
  have hfour := conditional_vector_field_memLp_four μ q hq W hW c g hg hrep
  exact ⟨g, hg, hg2, hfour.1, hfour.2.1, hrep, hbound2, hfour.2.2.2, hpair⟩

end AffineFKProof
