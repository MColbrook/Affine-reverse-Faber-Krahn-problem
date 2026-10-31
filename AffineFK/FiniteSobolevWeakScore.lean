module

public import AffineFK.FiniteSobolevRelativeScore

/-!
# The actual compact-test score identity on the unweighted H1 graph

The density is exactly the square of the completed graph's value. Its
score is constructed from that graph's actual gradient, and its weak
identity follows from the proved square-density product rule. No weak
score equation is assumed. All compact-test products are genuinely L1.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

def finiteSobolevGraphScore (n : ℕ) (v : unweightedSobolevGraph n) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  finiteSobolevRelativeScore n (unweightedValue n v) (unweightedGradient n v)

theorem finiteSobolevGraphScore_stronglyMeasurable (n : ℕ) (v : unweightedSobolevGraph n) :
    StronglyMeasurable (finiteSobolevGraphScore n v) := by
  exact ((measurable_const.div (Lp.stronglyMeasurable (unweightedValue n v)).measurable).smul
    (Lp.stronglyMeasurable (unweightedGradient n v)).measurable |>.add measurable_id).stronglyMeasurable

theorem finiteSobolevGraphScore_memLp_energy (n : ℕ) (v : unweightedSobolevGraph n)
    (hxf : MemLp (fun x => unweightedValue n v x • x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (finiteSobolevGraphScore n v) 2
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
      (∫ x, ‖finiteSobolevGraphScore n v x‖ ^ 2
        ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ≤
        ∫ x, ‖(2 : ℝ) • unweightedGradient n v x + unweightedValue n v x • x‖ ^ 2 :=
  finiteSobolevRelativeScore_memLp_energy n _ _
    (Lp.stronglyMeasurable (unweightedValue n v)) (Lp.stronglyMeasurable (unweightedGradient n v))
    (((Lp.memLp (unweightedGradient n v)).const_smul (2 : ℝ)).add hxf)

theorem finiteSobolevGraphScore_component_identity (n : ℕ) (v : unweightedSobolevGraph n)
    (hxf : MemLp (fun x => unweightedValue n v x • x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))]
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => finiteSobolevGraphScore n v x i * φ x)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * φ x)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
    Integrable (partialTest n i φ)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
    (∫ x, finiteSobolevGraphScore n v x i * φ x
      ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) =
      (∫ x : EuclideanSpace ℝ (Fin n), x i * φ x
        ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) -
      ∫ x, partialTest n i φ x ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2) := by
  let f := unweightedValue n v
  let g := unweightedGradient n v
  let ν := densityMeasure n (fun x => (f x) ^ 2)
  have hf := Lp.memLp f
  have hg := Lp.memLp g
  have hφ : MemLp φ 2 ν := testFunction_memLp_two n ν φ
  have hscore := (finiteSobolevGraphScore_memLp_energy n v hxf).1
  have hscoreφ := (hscore.eval_piLp i).integrable_mul hφ
  have hxi := (finiteSobolev_coordinate_memLp n f (Lp.stronglyMeasurable f).measurable hxf).eval_piLp i
  have hxφ : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * φ x) ν := hxi.integrable_mul hφ
  have hdφ : Integrable (partialTest n i φ) ν :=
    (testFunction_memLp_two n ν (partialTest n i φ)).integrable (by norm_num)
  refine ⟨hscoreφ, hxφ, hdφ, ?_⟩
  have hfirst : Integrable (fun x => (2 * f x * g x i) * φ x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hmul := (hf.integrable_mul (hg.eval_piLp i)).const_mul 2
    apply (hmul.mul_bdd φ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x =>
        (TestFunction.toBoundedContinuousFunctionCLM ℝ φ).norm_coe_le_norm x)).congr
    exact Filter.Eventually.of_forall fun x => by dsimp; ring
  have hsecond : Integrable (fun x => (f x) ^ 2 * (x i * φ x)) volume :=
    (finiteSobolev_density_integrable_iff n f (Lp.stronglyMeasurable f).measurable _).mp hxφ
  have hsplit : (∫ x, (f x) ^ 2 * (finiteSobolevGraphScore n v x i * φ x)) =
      (∫ x, (2 * f x * g x i) * φ x) + (∫ x, (f x) ^ 2 * (x i * φ x)) := by
    rw [← integral_add hfirst hsecond]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      have hw := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i)
        (finiteSobolevRelativeScore_weighted n f g x)
      simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul] at hw
      change (f x) ^ 2 * (finiteSobolevRelativeScore n f g x i * φ x) = _
      calc
        _ = ((f x) ^ 2 * finiteSobolevRelativeScore n f g x i) * φ x := by ring
        _ = _ := by rw [hw]; ring
  have hweak := unweighted_graph_square_product_rule n v i φ
  change (∫ x, (f x) ^ 2 * partialTest n i φ x) = -(∫ x, (2 * f x * g x i) * φ x) at hweak
  rw [finiteSobolev_density_integral n f (Lp.stronglyMeasurable f).measurable,
    finiteSobolev_density_integral n f (Lp.stronglyMeasurable f).measurable,
    finiteSobolev_density_integral n f (Lp.stronglyMeasurable f).measurable, hsplit]
  linarith

theorem finiteSobolevGraphScore_vector_identity (n : ℕ) (v : unweightedSobolevGraph n)
    (hxf : MemLp (fun x => unweightedValue n v x • x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))]
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n))) :
    Integrable (fun x => ⟪finiteSobolevGraphScore n v x, F x⟫)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
    Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
    (∫ x, ⟪finiteSobolevGraphScore n v x, F x⟫
      ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) =
      ∫ x, ⟪x, F x⟫ - vectorDivergence n F x
        ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2) := by
  let ν := densityMeasure n (fun x => (unweightedValue n v x) ^ 2)
  have hc (i : Fin n) := finiteSobolevGraphScore_component_identity n v hxf i (vectorComponentTest n i F)
  have hleft : (fun x => ⟪finiteSobolevGraphScore n v x, F x⟫) =
      (fun x => ∑ i : Fin n, finiteSobolevGraphScore n v x i * vectorComponentTest n i F x) := by
    funext x
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      vectorComponentTest_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    exact mul_comm _ _
  have hr (i : Fin n) : Integrable (fun x => x i * vectorComponentTest n i F x -
      partialTest n i (vectorComponentTest n i F) x) ν :=
    (hc i).2.1.sub (hc i).2.2.1
  have hright : Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) ν := by
    simp_rw [vector_stein_left_sum]
    exact integrable_finsetSum Finset.univ fun i _hi => hr i
  refine ⟨?_, hright, ?_⟩
  · change Integrable (fun x => ⟪finiteSobolevGraphScore n v x, F x⟫) ν
    rw [hleft]
    exact integrable_finsetSum Finset.univ fun i _hi => (hc i).1
  · change (∫ x, ⟪finiteSobolevGraphScore n v x, F x⟫ ∂ν) =
      ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν
    rw [hleft]
    simp_rw [vector_stein_left_sum]
    rw [integral_finsetSum Finset.univ (fun i _hi => (hc i).1),
      integral_finsetSum Finset.univ (fun i _hi => hr i)]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [integral_sub (hc i).2.1 (hc i).2.2.1]
    exact (hc i).2.2.2

theorem finiteSobolev_x_value_memLp_of_second_moment (n : ℕ)
    (v : unweightedSobolevGraph n)
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))) :
    MemLp (fun x => unweightedValue n v x • x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hmeas : StronglyMeasurable (fun x => unweightedValue n v x • x) :=
    ((Lp.stronglyMeasurable (unweightedValue n v)).measurable.smul measurable_id).stronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr
  have hweighted := (finiteSobolev_density_integrable_iff n (unweightedValue n v)
    (Lp.stronglyMeasurable (unweightedValue n v)).measurable (fun x => ‖x‖ ^ 2)).mp hsecond
  apply hweighted.congr
  exact Filter.Eventually.of_forall fun x => by
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem finiteSobolev_graph_relative_score (n : ℕ) (v : unweightedSobolevGraph n)
    [IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))) :
    StronglyMeasurable (finiteSobolevGraphScore n v) ∧
    MemLp (finiteSobolevGraphScore n v) 2
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
    (∫ x, ‖finiteSobolevGraphScore n v x‖ ^ 2
      ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ≤
      (∫ x, ‖(2 : ℝ) • unweightedGradient n v x + unweightedValue n v x • x‖ ^ 2) ∧
    ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      Integrable (fun x => ⟪finiteSobolevGraphScore n v x, F x⟫)
        (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
      Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x)
        (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) ∧
      (∫ x, ⟪finiteSobolevGraphScore n v x, F x⟫
        ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) =
        ∫ x, ⟪x, F x⟫ - vectorDivergence n F x
          ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2) := by
  have hxf := finiteSobolev_x_value_memLp_of_second_moment n v hsecond
  have hscore := finiteSobolevGraphScore_memLp_energy n v hxf
  exact ⟨finiteSobolevGraphScore_stronglyMeasurable n v, hscore.1, hscore.2,
    fun F => finiteSobolevGraphScore_vector_identity n v hxf F⟩

end AffineFKProof
