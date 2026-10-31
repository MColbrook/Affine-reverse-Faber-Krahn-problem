module

public import AffineFK.SobolevDensityProductRule
public import AffineFK.VectorSteinIdentity

/-!
# A weak relative score for a finite unweighted Sobolev square density

For the genuine H1 value f and gradient g, the field 2g/f+x is defined
also on the zero set of f by Lean's ordinary total division. Multiplication
by the density f squared removes this zero-set convention. Its weighted
L2 energy is bounded by the actual square-root-density Sobolev energy;
no assertion that g vanishes on the zero set is required for this bound.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

def finiteSobolevRelativeScore (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (2 / f x) • g x + x

theorem finiteSobolevRelativeScore_weighted (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    (f x) ^ 2 • finiteSobolevRelativeScore n f g x =
      (2 * f x) • g x + (f x) ^ 2 • x := by
  ext i
  simp only [finiteSobolevRelativeScore, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  by_cases hx : f x = 0
  · simp [hx]
  · field_simp [hx]

theorem finiteSobolevRelativeScore_energy_pointwise (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    (f x) ^ 2 * ‖finiteSobolevRelativeScore n f g x‖ ^ 2 ≤
      ‖(2 : ℝ) • g x + f x • x‖ ^ 2 := by
  by_cases hx : f x = 0
  · simp only [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact sq_nonneg _
  · have heq : f x • finiteSobolevRelativeScore n f g x =
        (2 : ℝ) • g x + f x • x := by
      simp only [finiteSobolevRelativeScore, smul_add, smul_smul]
      congr 1
      field_simp [hx]
    calc
      _ = ‖f x • finiteSobolevRelativeScore n f g x‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ _ := by rw [heq]

theorem finiteSobolev_density_integral (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    (q : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, q x ∂densityMeasure n (fun x => (f x) ^ 2)) =
      ∫ x, (f x) ^ 2 * q x := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul
    (hf.pow_const 2).ennreal_ofReal (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (ENNReal.ofReal ((f x) ^ 2)).toReal * q x = _
    rw [ENNReal.toReal_ofReal (sq_nonneg (f x))]

theorem finiteSobolev_density_integrable_iff (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    (q : EuclideanSpace ℝ (Fin n) → ℝ) :
    Integrable q (densityMeasure n (fun x => (f x) ^ 2)) ↔
      Integrable (fun x => (f x) ^ 2 * q x) volume := by
  unfold densityMeasure
  have h := integrable_withDensity_iff_integrable_smul'
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (g := q) (hf.pow_const 2).ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul] using h

theorem finiteSobolevRelativeScore_memLp_energy (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
    (hA : MemLp (fun x => (2 : ℝ) • g x + f x • x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (finiteSobolevRelativeScore n f g) 2 (densityMeasure n (fun x => (f x) ^ 2)) ∧
      (∫ x, ‖finiteSobolevRelativeScore n f g x‖ ^ 2 ∂densityMeasure n (fun x => (f x) ^ 2)) ≤
        ∫ x, ‖(2 : ℝ) • g x + f x • x‖ ^ 2 := by
  have hS : StronglyMeasurable (finiteSobolevRelativeScore n f g) := by
    exact ((measurable_const.div hf.measurable).smul hg.measurable |>.add measurable_id).stronglyMeasurable
  have hA2 := (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA
  have hweighted : Integrable (fun x => (f x) ^ 2 *
      ‖finiteSobolevRelativeScore n f g x‖ ^ 2) volume := by
    apply hA2.mono' ((hf.pow 2).mul (hS.norm.pow 2)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact finiteSobolevRelativeScore_energy_pointwise n f g x
  have hS2 : Integrable (fun x => ‖finiteSobolevRelativeScore n f g x‖ ^ 2)
      (densityMeasure n (fun x => (f x) ^ 2)) :=
    (finiteSobolev_density_integrable_iff n f hf.measurable _).mpr hweighted
  refine ⟨(memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).mpr hS2, ?_⟩
  rw [finiteSobolev_density_integral n f hf.measurable]
  exact integral_mono_ae hweighted hA2
    (Filter.Eventually.of_forall fun x => finiteSobolevRelativeScore_energy_pointwise n f g x)

theorem finiteSobolev_coordinate_memLp (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    (hxf : MemLp (fun x => f x • x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x) 2
      (densityMeasure n (fun x => (f x) ^ 2)) := by
  apply (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr
  apply (finiteSobolev_density_integrable_iff n f hf _).mpr
  apply ((memLp_two_iff_integrable_sq_norm hxf.aestronglyMeasurable).mp hxf).congr
  exact Filter.Eventually.of_forall fun x => by
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, id_eq]

end AffineFKProof
