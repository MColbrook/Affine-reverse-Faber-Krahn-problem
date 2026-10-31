module

public import AffineFK.UnweightedSobolevGraph

/-!
# Bounded measurable coefficient fields act continuously on Lebesgue L2

The coefficient is an actual field of continuous real linear maps. Its
pointwise norm bound proves the actual L2 membership and operator bound,
without finite total volume. These operators supply the value-gradient
multiplier and zero-extension maps for the genuine Dirichlet space.
Mathlib's Lp, strong measurability and norm-bound results are reused with
their Apache-2.0 contributor attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory

theorem l2CoefficientField_memLp (n : ℕ) {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : EuclideanSpace ℝ (Fin n) → F →L[ℝ] G) (hA : StronglyMeasurable A)
    (C : ℝ) (hbound : ∀ x, ‖A x‖ ≤ C)
    (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x => A x (f x)) 2 volume := by
  apply MemLp.of_le_mul (c := C) (Lp.memLp f)
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk (Lp.memLp f).aestronglyMeasurable))
  exact Filter.Eventually.of_forall fun x =>
    ((A x).le_opNorm (f x)).trans (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

def l2CoefficientFieldLinear (n : ℕ) {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : EuclideanSpace ℝ (Fin n) → F →L[ℝ] G) (hA : StronglyMeasurable A)
    (C : ℝ) (hbound : ∀ x, ‖A x‖ ≤ C) :
    Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ[ℝ]
      Lp G 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun f := (l2CoefficientField_memLp n A hA C hbound f).toLp (fun x => A x (f x))
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (l2CoefficientField_memLp n A hA C hbound (f + g)),
      MemLp.coeFn_toLp (l2CoefficientField_memLp n A hA C hbound f),
      MemLp.coeFn_toLp (l2CoefficientField_memLp n A hA C hbound g),
      Lp.coeFn_add f g,
      Lp.coeFn_add ((l2CoefficientField_memLp n A hA C hbound f).toLp _)
        ((l2CoefficientField_memLp n A hA C hbound g).toLp _)] with x hfg hf hg ha hb
    rw [hfg, hb]
    simp only [Pi.add_apply]
    rw [hf, hg, ha]
    simp only [Pi.add_apply]
    exact (A x).map_add _ _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (l2CoefficientField_memLp n A hA C hbound (c • f)),
      MemLp.coeFn_toLp (l2CoefficientField_memLp n A hA C hbound f),
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((l2CoefficientField_memLp n A hA C hbound f).toLp _)] with x hcf hf ha hb
    simp only [RingHom.id_apply]
    rw [hcf, hb]
    simp only [Pi.smul_apply]
    rw [hf, ha]
    simp only [Pi.smul_apply]
    exact (A x).map_smul c _

theorem l2CoefficientFieldLinear_coe (n : ℕ) {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : EuclideanSpace ℝ (Fin n) → F →L[ℝ] G) (hA : StronglyMeasurable A)
    (C : ℝ) (hbound : ∀ x, ‖A x‖ ≤ C)
    (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    l2CoefficientFieldLinear n A hA C hbound f =ᵐ[volume] fun x => A x (f x) :=
  MemLp.coeFn_toLp (l2CoefficientField_memLp n A hA C hbound f)

def l2CoefficientField (n : ℕ) {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : EuclideanSpace ℝ (Fin n) → F →L[ℝ] G) (hA : StronglyMeasurable A)
    (C : ℝ) (hbound : ∀ x, ‖A x‖ ≤ C) :
    Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp G 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (l2CoefficientFieldLinear n A hA C hbound).mkContinuous C (fun f => by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [l2CoefficientFieldLinear_coe n A hA C hbound f] with x hx
    rw [hx]
    exact ((A x).le_opNorm (f x)).trans
      (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)))

theorem l2CoefficientField_coe (n : ℕ) {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : EuclideanSpace ℝ (Fin n) → F →L[ℝ] G) (hA : StronglyMeasurable A)
    (C : ℝ) (hbound : ∀ x, ‖A x‖ ≤ C)
    (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    l2CoefficientField n A hA C hbound f =ᵐ[volume] fun x => A x (f x) :=
  l2CoefficientFieldLinear_coe n A hA C hbound f

end AffineFKProof
