module

public import AffineFK.OUDensityPDEScoreJoint
public import AffineFK.OUFisherUniformBounds
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Genuine space/time integrability of positive-time Fisher and Hessian energy

The actual conditional Gaussian estimates provide explicit majorants on
every positive compact time interval. Joint measurability and Bochner
Fubini then give genuine space/time L1 statements. No time-integrability,
Fisher derivative, or dissipation identity is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

theorem positive_time_nonnegative_integrable_prod (n : ℕ)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : Measurable (fun p : {r : ℝ // 0 < r} × EuclideanSpace ℝ (Fin n) => f p.1.val p.2))
    (hi : ∀ r : ℝ, 0 < r → Integrable (f r))
    (hn : ∀ r : ℝ, 0 < r → ∀ x, 0 ≤ f r x)
    (s t : ℝ) (hs : 0 < s) (B : ℝ)
    (hb : ∀ r ∈ Icc s t, (∫ x, f r x) ≤ B) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin n) => f p.1 p.2)
      ((volume.restrict (Ioc s t)).prod volume) := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ := volume.restrict (Ioc s t)
  let W : ℝ × E → {r : ℝ // 0 < r} × E := fun p =>
    (⟨max p.1 (s / 2), (half_pos hs).trans_le (le_max_right _ _)⟩, p.2)
  have hW : Continuous W := by dsimp [W]; fun_prop
  let F : ℝ × E → ℝ := fun p => f (max p.1 (s / 2)) p.2
  have hFm : StronglyMeasurable F := (hm.comp hW.measurable).stronglyMeasurable
  have hFi : Integrable F (μ.prod volume) := by
    apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall fun r => hi _ ((half_pos hs).trans_le (le_max_right _ _)), ?_⟩
    apply (integrable_const B).mono' hFm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 < r := hs.trans hr.1
    have hmax : max r (s / 2) = r := max_eq_left (by linarith [hr.1])
    have heq : (∫ x : E, ‖F (r, x)‖) = ∫ x, f r x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [F]
        rw [hmax, Real.norm_eq_abs, abs_of_nonneg (hn r hr0 x)]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _), heq]
    exact hb r ⟨hr.1.le, hr.2⟩
  apply hFi.congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure E))).ae
    (ae_restrict_mem measurableSet_Ioc)] with p hp
  dsimp only [F]
  rw [max_eq_left (by linarith [hp.1])]

theorem ou_inverse_scale_four_le (s r : ℝ) (hs : 0 < s) (hsr : s ≤ r) :
    ((Real.sqrt (1 - Real.exp (-2 * r)))⁻¹) ^ 4 ≤
      ((Real.sqrt (1 - Real.exp (-2 * s)))⁻¹) ^ 4 := by
  have hr : 0 < r := hs.trans_le hsr
  have he : Real.exp (-2 * r) ≤ Real.exp (-2 * s) := Real.exp_le_exp.mpr (by linarith)
  have hb : Real.sqrt (1 - Real.exp (-2 * s)) ≤ Real.sqrt (1 - Real.exp (-2 * r)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hi := (inv_le_inv₀ (ou_smoothing_scale_domain r hr).2.1
    (ou_smoothing_scale_domain s hs).2.1).mpr hb
  exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hi _

theorem smooth_density_weight_integrable (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable ρ)
    (hn : ∀ x, 0 ≤ ρ x) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f (densityMeasure n ρ)) :
    Integrable (fun x => ρ x * f x) volume := by
  have h := (integrable_withDensity_iff_integrable_smul'
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (g := f)
    hm.ennreal_ofReal (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hf
  simpa only [ENNReal.toReal_ofReal (hn _), smul_eq_mul] using h

theorem ou_ordinary_fisher_density_integrable_prod (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (s t : ℝ) (hs : 0 < s) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      ‖gradient (fun x => Real.log (gaussianSmoothingDensity n ν (Real.exp (-p.1))
        (Real.sqrt (1 - Real.exp (-2 * p.1))) x)) p.2‖ ^ 2 *
      gaussianSmoothingDensity n ν (Real.exp (-p.1)) (Real.sqrt (1 - Real.exp (-2 * p.1))) p.2)
      ((volume.restrict (Ioc s t)).prod volume) := by
  let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
    gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
  let score : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun r => gradient (fun x => Real.log (ρ r x))
  let f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r x => ‖score r x‖ ^ 2 * ρ r x
  have hn (r : ℝ) (hr : 0 < r) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ f r x :=
    mul_nonneg (sq_nonneg _) (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain r hr).2.1 x).le
  have hi (r : ℝ) (hr : 0 < r) : Integrable (f r) := by
    have h := (gaussianSmoothing_ordinary_fisher_energy_bound n ν (Real.exp (-r))
      (Real.sqrt (1 - Real.exp (-2 * r))) (ou_smoothing_scale_domain r hr).2.1).1
    have hw := smooth_density_weight_integrable n (ρ r)
      (gaussianSmoothingDensity_continuous n ν _ _).measurable
      (fun x => (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain r hr).2.1 x).le) _ h
    exact hw.congr (Filter.Eventually.of_forall fun x => by
      change ρ r x * ‖score r x‖ ^ 2 = ‖score r x‖ ^ 2 * ρ r x
      exact mul_comm _ _)
  apply positive_time_nonnegative_integrable_prod n f
    (ou_ordinary_fisher_density_joint_continuous n ν).measurable hi hn s t hs
    (1 + ((Real.sqrt (1 - Real.exp (-2 * s)))⁻¹) ^ 4 * ((n : ℝ) * (n + 2)))
  intro r hr
  have hr0 : 0 < r := hs.trans_le hr.1
  have heq : (∫ x, f r x) = ∫ x, ‖score r x‖ ^ 2 ∂densityMeasure n (ρ r) := by
    rw [density_integral_eq n (ρ r) (gaussianSmoothingDensity_continuous n ν _ _)
      (fun x => (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain r hr0).2.1 x).le)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _
  rw [heq]
  exact (gaussianSmoothing_ordinary_fisher_energy_bound n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r))) (ou_smoothing_scale_domain r hr0).2.1).2.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (ou_inverse_scale_four_le s r hs hr.1) (by positivity)))

theorem ou_logHessian_energy_density_integrable_prod (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (s t : ℝ) (hs : 0 < s) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      gaussianSmoothingDensity n ν (Real.exp (-p.1)) (Real.sqrt (1 - Real.exp (-2 * p.1))) p.2 *
      matrixHilbertSchmidtSq (densityLogHessian n (gaussianSmoothingDensity n ν (Real.exp (-p.1))
        (Real.sqrt (1 - Real.exp (-2 * p.1)))) p.2))
      ((volume.restrict (Ioc s t)).prod volume) := by
  let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
    gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
  let H : ℝ → EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ := fun r => densityLogHessian n (ρ r)
  let f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r x => ρ r x * matrixHilbertSchmidtSq (H r x)
  have hmH : Measurable (fun p : {r : ℝ // 0 < r} × EuclideanSpace ℝ (Fin n) => matrixHilbertSchmidtSq (H p.1.val p.2)) := by
    unfold matrixHilbertSchmidtSq
    exact Finset.univ.measurable_fun_sum fun i _ => Finset.univ.measurable_fun_sum fun j _ =>
      (ou_logHessian_entry_joint_measurable n ν i j).pow_const 2
  have hm : Measurable (fun p : {r : ℝ // 0 < r} × EuclideanSpace ℝ (Fin n) => f p.1.val p.2) :=
    (ou_density_joint_continuous n ν).measurable.mul hmH
  have hn (r : ℝ) (hr : 0 < r) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ f r x :=
    mul_nonneg (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain r hr).2.1 x).le
      (matrixHilbertSchmidtSq_nonneg _)
  have hi (r : ℝ) (hr : 0 < r) : Integrable (f r) := by
    exact smooth_density_weight_integrable n (ρ r)
      (gaussianSmoothingDensity_continuous n ν _ _).measurable
      (fun x => (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain r hr).2.1 x).le) _
      (gaussianSmoothing_logHessian_squared_energy_bound n ν (Real.exp (-r))
        (Real.sqrt (1 - Real.exp (-2 * r))) (ou_smoothing_scale_domain r hr).2.1).1
  apply positive_time_nonnegative_integrable_prod n f hm hi hn s t hs
    (2 * ((Real.sqrt (1 - Real.exp (-2 * s)))⁻¹) ^ 4 * (n : ℝ) * (2 * n + 3))
  intro r hr
  have hr0 : 0 < r := hs.trans_le hr.1
  have heq : (∫ x, f r x) = ∫ x, matrixHilbertSchmidtSq (H r x) ∂densityMeasure n (ρ r) :=
    (density_integral_eq n (ρ r) (gaussianSmoothingDensity_continuous n ν _ _)
      (fun x => (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain r hr0).2.1 x).le) _).symm
  rw [heq]
  have hbound := (gaussianSmoothing_logHessian_squared_energy_bound n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r))) (ou_smoothing_scale_domain r hr0).2.1).2
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ou_inverse_scale_four_le s r hs hr.1) (by norm_num))
        (Nat.cast_nonneg _)) (by positivity)

end AffineFKProof
