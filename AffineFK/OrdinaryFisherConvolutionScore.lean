module

public import AffineFK.FiniteSobolevRelativeScore

/-!
# The ordinary weak score of an actual Sobolev square density

There is no moment hypothesis here. The graph is the closure of genuine
compact smooth value/gradient pairs over Lebesgue volume. Its product rule
therefore supplies the weak score equation. Division on the zero set uses
the usual total real division; multiplication by the density removes that
convention. The bound needs no assertion about the gradient on that set.

The density integral and L2 tools are reused from FiniteSobolevRelativeScore.
The underlying Bochner integral and Lp results are Mathlib results, with
their primary attributions retained in the imported developments.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

def ordinaryFisherGraphScore (n : ℕ) (v : unweightedSobolevGraph n) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => (2 / unweightedValue n v x) • unweightedGradient n v x

theorem ordinaryFisherGraphScore_stronglyMeasurable (n : ℕ)
    (v : unweightedSobolevGraph n) : StronglyMeasurable (ordinaryFisherGraphScore n v) := by
  exact ((measurable_const.div (Lp.stronglyMeasurable (unweightedValue n v)).measurable).smul
    (Lp.stronglyMeasurable (unweightedGradient n v)).measurable).stronglyMeasurable

theorem ordinaryFisherGraphScore_weighted (n : ℕ) (v : unweightedSobolevGraph n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (unweightedValue n v x) ^ 2 • ordinaryFisherGraphScore n v x =
      (2 * unweightedValue n v x) • unweightedGradient n v x := by
  ext i
  simp only [ordinaryFisherGraphScore, PiLp.smul_apply, smul_eq_mul]
  by_cases hx : unweightedValue n v x = 0
  · simp [hx]
  · field_simp [hx]

theorem ordinaryFisherGraphScore_energy_pointwise (n : ℕ) (v : unweightedSobolevGraph n)
    (x : EuclideanSpace ℝ (Fin n)) :
    (unweightedValue n v x) ^ 2 * ‖ordinaryFisherGraphScore n v x‖ ^ 2 ≤
      4 * ‖unweightedGradient n v x‖ ^ 2 := by
  by_cases hx : unweightedValue n v x = 0
  · simp only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    positivity
  · have heq : unweightedValue n v x • ordinaryFisherGraphScore n v x =
        (2 : ℝ) • unweightedGradient n v x := by
      simp only [ordinaryFisherGraphScore, smul_smul]
      congr 1
      field_simp [hx]
    calc
      _ = ‖unweightedValue n v x • ordinaryFisherGraphScore n v x‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ = 4 * ‖unweightedGradient n v x‖ ^ 2 := by
        rw [heq, norm_smul, mul_pow]
        norm_num
      _ ≤ _ := le_rfl

theorem ordinaryFisherGraphScore_memLp_energy (n : ℕ) (v : unweightedSobolevGraph n) :
    MemLp (ordinaryFisherGraphScore n v) 2
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
      (∫ x, ‖ordinaryFisherGraphScore n v x‖ ^ 2
        ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ≤
        4 * ∫ x, ‖unweightedGradient n v x‖ ^ 2 := by
  have hf := Lp.stronglyMeasurable (unweightedValue n v)
  have hs := ordinaryFisherGraphScore_stronglyMeasurable n v
  have hg := Lp.memLp (unweightedGradient n v)
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hw : Integrable (fun x => (unweightedValue n v x) ^ 2 *
      ‖ordinaryFisherGraphScore n v x‖ ^ 2) volume := by
    apply (hg2.const_mul 4).mono' ((hf.pow 2).mul (hs.norm.pow 2)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact ordinaryFisherGraphScore_energy_pointwise n v x
  have hs2 : Integrable (fun x => ‖ordinaryFisherGraphScore n v x‖ ^ 2)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) :=
    (finiteSobolev_density_integrable_iff n _ hf.measurable _).mpr hw
  refine ⟨(memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mpr hs2, ?_⟩
  rw [finiteSobolev_density_integral n _ hf.measurable, ← integral_const_mul]
  exact integral_mono_ae hw (hg2.const_mul 4)
    (Filter.Eventually.of_forall fun x => ordinaryFisherGraphScore_energy_pointwise n v x)

theorem ordinaryFisherGraphScore_component_identity (n : ℕ) (v : unweightedSobolevGraph n)
    [IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))]
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => ordinaryFisherGraphScore n v x i * φ x)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
    Integrable (partialTest n i φ)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
    (∫ x, ordinaryFisherGraphScore n v x i * φ x
      ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) =
        -(∫ x, partialTest n i φ x
          ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) := by
  let f := unweightedValue n v
  let g := unweightedGradient n v
  let ν := densityMeasure n (fun x => (f x) ^ 2)
  have hs := (ordinaryFisherGraphScore_memLp_energy n v).1
  have hleft := (hs.eval_piLp i).integrable_mul (testFunction_memLp_two n ν φ)
  have hright : Integrable (partialTest n i φ) ν :=
    (testFunction_memLp_two n ν (partialTest n i φ)).integrable (by norm_num)
  refine ⟨hleft, hright, ?_⟩
  have hweak := unweighted_graph_square_product_rule n v i φ
  rw [finiteSobolev_density_integral n f (Lp.stronglyMeasurable f).measurable,
    finiteSobolev_density_integral n f (Lp.stronglyMeasurable f).measurable]
  calc
    _ = ∫ x, (2 * f x * g x i) * φ x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        have hw := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i)
          (ordinaryFisherGraphScore_weighted n v x)
        simp only [PiLp.smul_apply, smul_eq_mul] at hw
        change (f x) ^ 2 * (ordinaryFisherGraphScore n v x i * φ x) = _
        calc
          _ = ((f x) ^ 2 * ordinaryFisherGraphScore n v x i) * φ x := by ring
          _ = _ := by rw [hw]
    _ = _ := by
      change (∫ x, (f x) ^ 2 * partialTest n i φ x) =
        -(∫ x, (2 * f x * g x i) * φ x) at hweak
      linarith

end AffineFKProof
