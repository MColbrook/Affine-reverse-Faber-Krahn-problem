module

public import AffineFK.GaussianKilledIntegral

/-! # Literal finite Gaussian killing iterates as nonzero L2 powers -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

def gaussianKillingIterateL2 (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (dirichletGaussianIterate_toReal_memLp n U hU hfin (Real.sqrt h) (Real.sqrt_pos.mpr hh) k 2).toLp
    (fun x => (dirichletGaussianIterate n U (Real.sqrt h) k x).toReal)

theorem gaussianKillingIterateL2_coe (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    (gaussianKillingIterateL2 n U hU hfin h hh k : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => (dirichletGaussianIterate n U (Real.sqrt h) k x).toReal := by
  unfold gaussianKillingIterateL2 MemLp.toLp
  exact AEEqFun.coeFn_mk _ _

theorem gaussianKillingIterateL2_zero_exterior (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    ∀ᵐ x ∂volume, x ∉ U → gaussianKillingIterateL2 n U hU hfin h hh k x=0 := by
  filter_upwards [gaussianKillingIterateL2_coe n U hU hfin h hh k] with x hx hnot
  rw [hx,dirichletGaussianIterate_zero_outside n U (Real.sqrt h) k x hnot,
    ENNReal.toReal_zero]

theorem gaussianKillingIterateL2_norm_pos (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    0 < ‖gaussianKillingIterateL2 n U hU.measurableSet hfin h hh k‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hae := gaussianKillingIterateL2_coe n U hU.measurableSet hfin h hh k
  rw [hz] at hae
  have hreal : (fun x => (dirichletGaussianIterate n U (Real.sqrt h) k x).toReal) =ᵐ[volume] 0 :=
    hae.symm.trans (Lp.coeFn_zero ℝ 2 volume)
  have hzero : dirichletGaussianIterate n U (Real.sqrt h) k =ᵐ[volume] 0 := by
    filter_upwards [hreal] with x hx
    have ht := dirichletGaussianIterate_ne_top n U (Real.sqrt h) (Real.sqrt_pos.mpr hh) k x
    exact (ENNReal.toReal_eq_zero_iff _).mp hx |>.resolve_right ht
  have hm := dirichletGaussianIterate_mass_pos n U hU hne (Real.sqrt h) (Real.sqrt_pos.mpr hh) k
  rw [lintegral_congr_ae hzero] at hm
  simpa using hm

theorem gaussianKillingIterateL2_step (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    gaussianKilledL2 n U hU h hh (gaussianKillingIterateL2 n U hU hfin h hh k) =
      gaussianKillingIterateL2 n U hU hfin h hh (k+1) := by
  let f := gaussianKillingIterateL2 n U hU hfin h hh k
  let F := dirichletGaussianIterate n U (Real.sqrt h) k
  have hf : U.indicator f =ᵐ[volume] fun y => (F y).toReal := by
    filter_upwards [gaussianKillingIterateL2_coe n U hU hfin h hh k] with y hy
    by_cases hm : y ∈ U
    · rw [indicator_of_mem hm]
      exact hy
    · rw [indicator_of_notMem hm]
      simp only [F,dirichletGaussianIterate_zero_outside n U (Real.sqrt h) k y hm,
        ENNReal.toReal_zero]
  have hconv (x : EuclideanSpace ℝ (Fin n)) :
      (∫ y, (dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal * U.indicator f y) =
      (∫⁻ y, dirichletGaussianKernel n (Real.sqrt h) (x-y) * F y).toReal := by
    calc
      _ = ∫ y, (dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal * (F y).toReal := by
        apply integral_congr_ae
        filter_upwards [hf] with y hy
        rw [hy]
      _ = _ := by
        have hm : Measurable (fun y => dirichletGaussianKernel n (Real.sqrt h) (x-y) * F y) :=
          ((dirichletGaussianKernel_measurable n (Real.sqrt h)).comp
            (measurable_const.sub measurable_id)).mul
              (dirichletGaussianIterate_measurable n U hU (Real.sqrt h) k)
        have ht : ∀ᵐ y ∂volume, dirichletGaussianKernel n (Real.sqrt h) (x-y) * F y < ∞ :=
          Eventually.of_forall fun y => lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
            (by unfold dirichletGaussianKernel; finiteness)
            (dirichletGaussianIterate_ne_top n U (Real.sqrt h) (Real.sqrt_pos.mpr hh) k y))
        simpa only [ENNReal.toReal_mul] using integral_toReal hm.aemeasurable ht
  apply Lp.ext
  filter_upwards [gaussianKilledL2_density_coe n U hU h hh f,
    gaussianKillingIterateL2_coe n U hU hfin h hh (k+1)] with x hx hnext
  rw [hx,hnext]
  by_cases hm : x ∈ U
  · rw [indicator_of_mem hm,hconv]
    simp only [dirichletGaussianIterate,dirichletGaussianStep,indicator_of_mem hm,F]
  · rw [indicator_of_notMem hm,dirichletGaussianIterate_zero_outside n U (Real.sqrt h) (k+1) x hm,
      ENNReal.toReal_zero]

theorem gaussianKillingIterateL2_eq_power (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (k : ℕ) :
    gaussianKillingIterateL2 n U hU hfin h hh k =
      ((gaussianKilledL2 n U hU h hh)^k) (gaussianKillingIterateL2 n U hU hfin h hh 0) := by
  induction k with
  | zero => simp only [pow_zero,one_apply_eq_self]
  | succ k hk => rw [← gaussianKillingIterateL2_step n U hU hfin h hh k,hk,
      pow_succ',mul_apply_eq_comp]

end AffineFKProof
