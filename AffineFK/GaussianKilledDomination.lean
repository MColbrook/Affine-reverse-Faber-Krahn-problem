module

public import AffineFK.GaussianKilledIntegral

/-! # A genuine Gaussian row bound in terms of the domain indicator -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

theorem gaussianL2_indicator_norm_integral_le (n : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x in U, ‖f x‖) ≤ ‖indicatorConstLp 2 hU hfin (1 : ℝ)‖ * ‖f‖ := by
  let af := (Lp.memLp f).norm.toLp (fun x => ‖f x‖)
  have hnorm : ‖af‖ = ‖f‖ := by
    rw [Lp.norm_toLp,eLpNorm_norm _ (Lp.aestronglyMeasurable f)]
    exact (Lp.norm_def f).symm
  have hi := L2.inner_indicatorConstLp_one (𝕜 := ℝ) hU hfin af
  have he : (∫ x in U, af x) = ∫ x in U, ‖f x‖ := by
    apply integral_congr_ae
    exact ae_restrict_of_ae (MemLp.coeFn_toLp (Lp.memLp f).norm)
  rw [he] at hi
  have hc := real_inner_le_norm (indicatorConstLp 2 hU hfin (1 : ℝ)) af
  rw [hi,hnorm] at hc
  exact hc

theorem gaussianKilledL2_indicator_domination (n : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ᵐ x ∂volume, ‖gaussianKilledL2 n U hU h hh f x‖ ≤
        C * ‖f‖ * indicatorConstLp 2 hU hfin (1 : ℝ) x := by
  obtain ⟨B,hB,hbound⟩ := gaussianKernel_toReal_uniform_bound n (Real.sqrt h) (Real.sqrt_pos.mpr hh)
  let g := indicatorConstLp 2 hU hfin (1 : ℝ)
  refine ⟨B*‖g‖,mul_nonneg hB (norm_nonneg _),?_⟩
  intro f
  have hfU := integrableOn_Lp_of_measure_ne_top f (by norm_num : (1 : ℝ≥0∞) ≤ 2) hfin
  have hind : Integrable (U.indicator (fun y => ‖f y‖)) volume :=
    (integrable_indicator_iff hU).mpr hfU.norm
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      ‖∫ y, (dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal * U.indicator f y‖ ≤
        (B*‖g‖)*‖f‖ := by
    have hm : AEStronglyMeasurable
        (fun y => (dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal * U.indicator f y) volume :=
      (((dirichletGaussianKernel_measurable n (Real.sqrt h)).comp
        (measurable_const.sub measurable_id)).ennreal_toReal.aestronglyMeasurable).mul
          ((Lp.aestronglyMeasurable f).indicator hU)
    have hb (y : EuclideanSpace ℝ (Fin n)) :
        ‖(dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal * U.indicator f y‖ ≤
        B * U.indicator (fun y => ‖f y‖) y := by
      by_cases hy : y ∈ U
      · rw [indicator_of_mem hy,indicator_of_mem hy,norm_mul,
          Real.norm_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
      · rw [indicator_of_notMem hy,indicator_of_notMem hy,mul_zero,norm_zero,mul_zero]
    have hrow := (hind.const_mul B).mono' hm (Eventually.of_forall hb)
    calc
      _ ≤ ∫ y, ‖(dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal * U.indicator f y‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ y, B * U.indicator (fun y => ‖f y‖) y :=
        integral_mono hrow.norm (hind.const_mul B) hb
      _ = B * ∫ y in U, ‖f y‖ := by rw [integral_const_mul,integral_indicator hU]
      _ ≤ B * (‖g‖*‖f‖) := mul_le_mul_of_nonneg_left
        (gaussianL2_indicator_norm_integral_le n U hU hfin f) hB
      _ = _ := (mul_assoc _ _ _).symm
  filter_upwards [gaussianKilledL2_density_coe n U hU h hh f,
    indicatorConstLp_coeFn (p := 2) (hs := hU) (hμs := hfin) (c := (1 : ℝ))]
      with x hK hg
  rw [hK,hg]
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx,indicator_of_mem hx,mul_one]
    exact hpoint x
  · rw [indicator_of_notMem hx,indicator_of_notMem hx,norm_zero,mul_zero]

end AffineFKProof
