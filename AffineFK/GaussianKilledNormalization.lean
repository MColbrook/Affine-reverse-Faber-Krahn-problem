module

public import AffineFK.GaussianKilledIterates

/-! # Actual normalized finite iterates and their pointwise log-concave representatives -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Filter
open scoped ENNReal

theorem gaussianKillingIterateL2_zero_eq_indicator (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) :
    gaussianKillingIterateL2 n U hU hfin h hh 0 = indicatorConstLp 2 hU hfin (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [gaussianKillingIterateL2_coe n U hU hfin h hh 0,
    indicatorConstLp_coeFn (p := 2) (hs := hU) (hμs := hfin) (c := (1 : ℝ))] with x hx hg
  rw [hx,hg]
  by_cases hm : x ∈ U <;> simp [dirichletGaussianIterate,hm]

def gaussianKillingNormalizedL2 (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  ‖gaussianKillingIterateL2 n U hU hfin h hh k‖⁻¹ • gaussianKillingIterateL2 n U hU hfin h hh k

def gaussianKillingNormalizedFunction (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖gaussianKillingIterateL2 n U hU hfin h hh k‖⁻¹ *
    (dirichletGaussianIterate n U (Real.sqrt h) k x).toReal

theorem gaussianKillingNormalizedL2_coe (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    (gaussianKillingNormalizedL2 n U hU hfin h hh k : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      gaussianKillingNormalizedFunction n U hU hfin h hh k := by
  filter_upwards [Lp.coeFn_smul ‖gaussianKillingIterateL2 n U hU hfin h hh k‖⁻¹
    (gaussianKillingIterateL2 n U hU hfin h hh k),gaussianKillingIterateL2_coe n U hU hfin h hh k]
      with x hs hx
  change (‖gaussianKillingIterateL2 n U hU hfin h hh k‖⁻¹ •
    gaussianKillingIterateL2 n U hU hfin h hh k) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hx,gaussianKillingNormalizedFunction]

theorem gaussianKillingNormalizedL2_norm (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    ‖gaussianKillingNormalizedL2 n U hU.measurableSet hfin h hh k‖ = 1 := by
  have hp := gaussianKillingIterateL2_norm_pos n U hU hne hfin h hh k
  simp only [gaussianKillingNormalizedL2,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_cancel₀ hp.ne']

theorem gaussianKillingNormalizedFunction_measurable (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    Measurable (gaussianKillingNormalizedFunction n U hU hfin h hh k) :=
  measurable_const.mul (dirichletGaussianIterate_measurable n U hU (Real.sqrt h) k).ennreal_toReal

theorem gaussianKillingNormalizedFunction_memLp (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    MemLp (gaussianKillingNormalizedFunction n U hU hfin h hh k) 2 volume :=
  (dirichletGaussianIterate_toReal_memLp n U hU hfin (Real.sqrt h) (Real.sqrt_pos.mpr hh) k 2).const_mul _

theorem gaussianKillingNormalizedFunction_nonneg (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ gaussianKillingNormalizedFunction n U hU hfin h hh k x :=
  mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) ENNReal.toReal_nonneg

theorem gaussianKillingNormalizedFunction_zero_exterior (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ U) :
    gaussianKillingNormalizedFunction n U hU hfin h hh k x=0 := by
  simp only [gaussianKillingNormalizedFunction,dirichletGaussianIterate_zero_outside n U (Real.sqrt h) k x hx,
    ENNReal.toReal_zero,mul_zero]

theorem gaussianKillingNormalizedFunction_even (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (hneg : ∀ x ∈ U,-x ∈ U) (h : ℝ) (hh : 0 < h) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianKillingNormalizedFunction n U hU hfin h hh k (-x)=
      gaussianKillingNormalizedFunction n U hU hfin h hh k x := by
  simp only [gaussianKillingNormalizedFunction,dirichletGaussianIterate_even n U hneg]

theorem gaussianKillingNormalizedFunction_logConcave (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (hconv : Convex ℝ U) (h : ℝ) (hh : 0 < h) (k : ℕ) :
    LogConcaveDensity (fun x => ENNReal.ofReal (gaussianKillingNormalizedFunction n U hU hfin h hh k x)) := by
  have he : (fun x => ENNReal.ofReal (gaussianKillingNormalizedFunction n U hU hfin h hh k x)) =
      fun x => ENNReal.ofReal ‖gaussianKillingIterateL2 n U hU hfin h hh k‖⁻¹ *
        dirichletGaussianIterate n U (Real.sqrt h) k x := by
    funext x
    rw [gaussianKillingNormalizedFunction,ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal (dirichletGaussianIterate_ne_top n U (Real.sqrt h) (Real.sqrt_pos.mpr hh) k x)]
  rw [he]
  exact logConcaveDensity_mul _ _ (logConcaveDensity_const _)
    (dirichletGaussianIterate_logConcave n U hU hconv (Real.sqrt h) k)

end AffineFKProof
