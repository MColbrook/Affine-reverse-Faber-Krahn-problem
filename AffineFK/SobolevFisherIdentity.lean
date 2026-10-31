module

public import AffineFK.SobolevFisherIntegration
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The square-root density energy identity

The compact-test weak product derivative is an explicit intermediate
input. The global coordinate integral is proved by cutoffs, and every
cross term is genuinely L1 by L2 Holder. Instantiation by the actual
unweighted Sobolev graph is a separate step.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace ENNReal

theorem sobolevFisher_square_root_coordinate (n : ℕ) (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hxf : MemLp (fun x => f x • x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n (fun x => (f x) ^ 2))]
    (hweak : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x) ^ 2 * partialTest n i φ x) = -(2 : ℝ) * (∫ x, f x * g x i * φ x)) :
    Integrable (fun x => (f x * x i) * g x i) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), (f x * x i) * g x i) = -(1 / 2 : ℝ) := by
  have hxi : MemLp (fun x => f x * x i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [PiLp.smul_apply, smul_eq_mul] using hxf.eval_piLp i
  have hcoord := hxi.integrable_mul (hg.eval_piLp i)
  have hd : Integrable (fun x => (2 : ℝ) * (f x * g x i)) :=
    (hf.integrable_mul (hg.eval_piLp i)).const_mul 2
  have hxd : Integrable (fun x => x i * ((2 : ℝ) * (f x * g x i))) := by
    apply (hcoord.const_mul 2).congr
    exact Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring
  have hw : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x) ^ 2 * partialTest n i φ x) =
        -(∫ x, ((2 : ℝ) * (f x * g x i)) * φ x) := by
    intro φ
    rw [hweak φ]
    have heq : (∫ x, ((2 : ℝ) * (f x * g x i)) * φ x) =
        2 * (∫ x, f x * g x i * φ x) := by
      calc
        _ = ∫ x, (2 : ℝ) * (f x * g x i * φ x) :=
          integral_congr_ae (Eventually.of_forall fun x => by dsimp; ring)
        _ = _ := integral_const_mul _ _
    rw [heq]
    ring
  have h := sobolevFisher_coordinate_integral_probability_density n i (fun x => (f x) ^ 2)
    (fun x => (2 : ℝ) * (f x * g x i)) hf.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg (f x)) hd hxd hw
  have heq : (∫ x, x i * ((2 : ℝ) * (f x * g x i))) =
      2 * (∫ x, (f x * x i) * g x i) := by
    calc
      _ = ∫ x, (2 : ℝ) * ((f x * x i) * g x i) :=
        integral_congr_ae (Eventually.of_forall fun x => by dsimp; ring)
      _ = _ := integral_const_mul _ _
  rw [heq] at h
  exact ⟨hcoord, by linarith⟩

theorem sobolevFisher_square_root_cross_integral (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hxf : MemLp (fun x => f x • x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n (fun x => (f x) ^ 2))]
    (hweak : ∀ i : Fin n, ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x) ^ 2 * partialTest n i φ x) = -(2 : ℝ) * (∫ x, f x * g x i * φ x)) :
    Integrable (fun x => ⟪g x, f x • x⟫) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), ⟪g x, f x • x⟫) = -(n : ℝ) / 2 := by
  have hi : Integrable (fun x => ⟪g x, f x • x⟫) :=
    memLp_one_iff_integrable.mp ((innerSL ℝ).memLp_of_bilin 1 hg hxf)
  have hc (i : Fin n) := sobolevFisher_square_root_coordinate n i f g hf hg hxf (hweak i)
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin n), ∑ i : Fin n, (f x * x i) * g x i := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
          PiLp.smul_apply, smul_eq_mul]
    _ = ∑ i : Fin n, ∫ x : EuclideanSpace ℝ (Fin n), (f x * x i) * g x i :=
      integral_finsetSum _ (fun i _ => (hc i).1)
    _ = _ := by
      simp only [(hc _).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem sobolevFisher_square_root_energy_identity (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hxf : MemLp (fun x => f x • x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n (fun x => (f x) ^ 2))]
    (hweak : ∀ i : Fin n, ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x) ^ 2 * partialTest n i φ x) = -(2 : ℝ) * (∫ x, f x * g x i * φ x)) :
    Integrable (fun x => ‖(2 : ℝ) • g x + f x • x‖ ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), ‖(2 : ℝ) • g x + f x • x‖ ^ 2) =
        4 * (∫ x, ‖g x‖ ^ 2) + (∫ x, ‖f x • x‖ ^ 2) - 2 * n := by
  have hsum := (hg.const_smul (2 : ℝ)).add hxf
  have hg2 := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hxf2 := (memLp_two_iff_integrable_sq_norm hxf.aestronglyMeasurable).mp hxf
  have hc := sobolevFisher_square_root_cross_integral n f g hf hg hxf hweak
  refine ⟨(memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).mp hsum, ?_⟩
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => ‖(2 : ℝ) • g x + f x • x‖ ^ 2) =
      (fun x => 4 * ‖g x‖ ^ 2 + 4 * ⟪g x, f x • x⟫ + ‖f x • x‖ ^ 2) := by
    funext x
    rw [norm_add_sq_real, norm_smul, real_inner_smul_left]
    norm_num [mul_pow] <;> ring
  rw [heq, integral_add
    (f := fun x : EuclideanSpace ℝ (Fin n) => 4 * ‖g x‖ ^ 2 + 4 * ⟪g x, f x • x⟫)
    (g := fun x => ‖f x • x‖ ^ 2)
    ((hg2.const_mul 4).add (hc.1.const_mul 4)) hxf2,
    integral_add (f := fun x : EuclideanSpace ℝ (Fin n) => 4 * ‖g x‖ ^ 2)
      (g := fun x => 4 * ⟪g x, f x • x⟫) (hg2.const_mul 4) (hc.1.const_mul 4),
    integral_const_mul, integral_const_mul, hc.2]
  ring

theorem sobolevFisher_square_root_moment (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hxf : MemLp (fun x => f x • x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable (fun x => ‖x‖ ^ 2) (densityMeasure n (fun x => (f x) ^ 2)) ∧
      (∫ x, ‖x‖ ^ 2 ∂densityMeasure n (fun x => (f x) ^ 2)) =
        ∫ x : EuclideanSpace ℝ (Fin n), ‖f x • x‖ ^ 2 := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal ((f x) ^ 2))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hf.aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal
  have hfinite : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ENNReal.ofReal ((f x) ^ 2) < ∞ :=
    Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => (ENNReal.ofReal ((f x) ^ 2)).toReal • ‖x‖ ^ 2) =
      (fun x => ‖f x • x‖ ^ 2) := by
    funext x
    rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hi := (memLp_two_iff_integrable_sq_norm hxf.aestronglyMeasurable).mp hxf
  constructor
  · apply (integrable_withDensity_iff_integrable_smul₀' hm hfinite).mpr
    rwa [heq]
  · rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀ hm hfinite, heq]

theorem sobolevFisher_square_root_relative_ordinary_identity (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hxf : MemLp (fun x => f x • x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n (fun x => (f x) ^ 2))]
    (hweak : ∀ i : Fin n, ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x) ^ 2 * partialTest n i φ x) = -(2 : ℝ) * (∫ x, f x * g x i * φ x)) :
    Integrable (fun x => ‖(2 : ℝ) • g x + f x • x‖ ^ 2) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x : EuclideanSpace ℝ (Fin n), ‖(2 : ℝ) • g x + f x • x‖ ^ 2) =
        4 * (∫ x, ‖g x‖ ^ 2) +
          (∫ x, ‖x‖ ^ 2 ∂densityMeasure n (fun x => (f x) ^ 2)) - 2 * n := by
  have he := sobolevFisher_square_root_energy_identity n f g hf hg hxf hweak
  refine ⟨he.1, ?_⟩
  rw [(sobolevFisher_square_root_moment n f hf hxf).2]
  exact he.2

end AffineFKProof
