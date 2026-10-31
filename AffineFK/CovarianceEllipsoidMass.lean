module

public import AffineFK.CovarianceEllipsoidMoment
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A genuine covariance ellipsoid carrying at least half the probability

The norm-square moment is derived in CovarianceEllipsoidMoment. Markov's
inequality then gives the mass of the literal translated square-root
ellipsoid; no ellipsoid mass or desired moment is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix Set Metric
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace ENNReal

def covarianceEllipsoidSet (n : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n)) (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖covarianceWhiteningLinear n (covarianceEllipsoidMomentMatrix n μ m) hM (x-m)‖ ≤
    Real.sqrt (2*(n : ℝ))}

theorem covarianceEllipsoidSet_inverse_image (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n))
    (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    covarianceEllipsoidSet n μ m hM =
      (fun z => m+(covarianceWhiteningLinear n (covarianceEllipsoidMomentMatrix n μ m) hM).symm z) ''
        closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ))) := by
  let W := covarianceWhiteningLinear n (covarianceEllipsoidMomentMatrix n μ m) hM
  ext x
  constructor
  · intro hx
    change ‖W (x-m)‖ ≤ Real.sqrt (2*(n : ℝ)) at hx
    refine ⟨W (x-m),?_,?_⟩
    · simpa only [mem_closedBall,dist_zero_right] using hx
    · change m+W.symm (W (x-m)) = x
      rw [W.symm_apply_apply]
      abel
  · rintro ⟨z,hz,rfl⟩
    change ‖W ((m+W.symm z)-m)‖ ≤ _
    rw [add_sub_cancel_left,W.apply_symm_apply]
    simpa only [mem_closedBall,dist_zero_right] using hz

theorem covarianceEllipsoid_inverse_sqrt_apply (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (z : EuclideanSpace ℝ (Fin n)) :
    (covarianceWhiteningLinear n M hM).symm z =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (CFC.sqrt M) z := by
  rw [covarianceWhiteningLinear_inverse_apply,covarianceWhiteningMatrix,
    Matrix.nonsing_inv_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (covariance_sqrt_posDef n M hM).det_pos.ne')]

theorem covarianceEllipsoidSet_sqrt_image (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n))
    (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    covarianceEllipsoidSet n μ m hM =
      (fun z => m+Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (CFC.sqrt (covarianceEllipsoidMomentMatrix n μ m)) z) ''
          closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ))) := by
  rw [covarianceEllipsoidSet_inverse_image]
  congr 1
  funext z
  rw [covarianceEllipsoid_inverse_sqrt_apply]

theorem covarianceEllipsoidSet_compact (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n))
    (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    IsCompact (covarianceEllipsoidSet n μ m hM) := by
  rw [covarianceEllipsoidSet_inverse_image]
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))).image (continuous_const.add
    (covarianceWhiteningLinear n _ hM).symm.continuous)

theorem covarianceEllipsoidSet_mass_real (n : ℕ) (hn : 0 < n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (m : EuclideanSpace ℝ (Fin n)) (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    (1/2 : ℝ) ≤ μ.real (covarianceEllipsoidSet n μ m hM) := by
  let W := covarianceWhiteningLinear n (covarianceEllipsoidMomentMatrix n μ m) hM
  let f := fun x : EuclideanSpace ℝ (Fin n) => ‖W (x-m)‖^2
  have hF := covarianceEllipsoidWhitened_memLp n μ hX m hM
  have hfInt : Integrable f μ :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hmoment : (∫ x, f x ∂μ) = (n : ℝ) :=
    covarianceEllipsoidWhitened_second_moment n μ hX m hM
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖W (x-m)‖) hfInt (2*(n : ℝ))
  rw [hmoment] at hMarkov
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have htail : μ.real {x | 2*(n : ℝ) ≤ f x} ≤ (1/2 : ℝ) := by
    have hleft : μ.real {x | 2*(n : ℝ) ≤ f x} * (2*(n : ℝ)) ≤ (n : ℝ) := by
      simpa only [mul_comm] using hMarkov
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hnpos)).mpr hleft
    have heq : (n : ℝ)/(2*(n : ℝ)) = (1/2 : ℝ) := by field_simp
    exact h.trans_eq heq
  have hsub : (covarianceEllipsoidSet n μ m hM)ᶜ ⊆ {x | 2*(n : ℝ) ≤ f x} := by
    intro x hx
    change ¬‖W (x-m)‖ ≤ Real.sqrt (2*(n : ℝ)) at hx
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg (2*(n : ℝ))) (le_of_lt (lt_of_not_ge hx)) 2
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hnpos.le)] at hsq
    exact hsq
  have hcompl : μ.real (covarianceEllipsoidSet n μ m hM)ᶜ ≤ (1/2 : ℝ) :=
    (measureReal_mono hsub).trans htail
  have hadd := measureReal_add_measureReal_compl (μ := μ)
    (covarianceEllipsoidSet_compact n μ m hM).measurableSet
  rw [probReal_univ] at hadd
  linarith

theorem covarianceEllipsoidSet_mass (n : ℕ) (hn : 0 < n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (m : EuclideanSpace ℝ (Fin n)) (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    (1/2 : ℝ≥0∞) ≤ μ (covarianceEllipsoidSet n μ m hM) := by
  apply (ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top _ _)).mp
  simpa only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,measureReal_def] using
    covarianceEllipsoidSet_mass_real n hn μ hX m hM

end AffineFKProof
