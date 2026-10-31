module

public import AffineFK.OUFisherMeasureCalculus
public import AffineFK.OUFisherAEDerivative
public import AffineFK.GaussianSmoothingIsotropy
public import AffineFK.FisherInformationMeasureOU

/-!
# Actual numerical relative Fisher dissipation for isotropic OU input

Literal input means and unit raw covariance give the actual output
isotropy. The canonical Sobolev information is then J-n, and the genuine
relative-score Hessian energy is K-2J+n. The already proved ordinary
identity yields the manuscript's relative identity and its almost-
everywhere derivative. No smooth initial density or finite initial
information assumption is needed for this positive-time statement.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Interval ENNReal

theorem ou_isotropic_relativeFisher_toReal (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (r : ℝ) (hr : 0 < r) :
    relativeFisherMeasure n (ouInitialLaw n ν r) ≠ (∞ : ℝ≥0∞) ∧
    (relativeFisherMeasure n (ouInitialLaw n ν r)).toReal =
      (∫ x, ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν (Real.exp (-r))
        (Real.sqrt (1 - Real.exp (-2 * r))) y)) x‖ ^ 2 *
          gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r))) x) - n := by
  let a := Real.exp (-r)
  let b := Real.sqrt (1 - Real.exp (-2 * r))
  let ρ := gaussianSmoothingDensity n ν a b
  let μ := densityMeasure n ρ
  have hb : 0 < b := (ou_smoothing_scale_domain r hr).2.1
  have hμ : ouInitialLaw n ν r = μ := gaussianSmoothingDensity_law n ν a b hb
  have : IsProbabilityMeasure μ := by rw [← hμ]; infer_instance
  have hout := gaussianSmoothing_density_isotropy n ν hmean hcov a b hb (ou_smoothing_scale_domain r hr).2.2
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ :=
    memLp_piLp_iff.mpr fun i => (hout.1 i).1
  have hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mp hX
  have hmoment : (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 ∂μ) = n := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    have hsqi (i : Fin n) : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2) μ := by
      simpa only [id_eq] using (hX.eval_piLp i).integrable_sq
    rw [integral_finsetSum Finset.univ fun i _ => hsqi i]
    have hi (i : Fin n) : (∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2 ∂μ) = 1 := by
      simpa only [pow_two, ite_true] using (hout.2 i i).2
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hJ := gaussianSmoothing_ordinaryFisherMeasure_eq_energy n ν a b hb
  have hI := fisherMeasure_unit_second_moment_identity n μ hJ.1 hsecond hmoment
  rw [hμ]
  refine ⟨hI.1, ?_⟩
  rw [hI.2, hJ.2]

theorem ou_relative_hessian_energy_identity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (r : ℝ) (hr : 0 < r) :
    let ρ := gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
    (∫ x, ∑ i : Fin n, ‖gradient (fun y => gaussianRelativeScore n ρ y i) x‖ ^ 2 ∂ouInitialLaw n ν r) =
      (∫ x, ρ x * matrixHilbertSchmidtSq (densityLogHessian n ρ x)) -
        2 * (∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ρ x) + n := by
  let ρ := gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
  have hb := (ou_smoothing_scale_domain r hr).2.1
  have h := (gaussianSmoothing_relative_hessian_energy_identity n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r))) hb).2
  have hμ : ouInitialLaw n ν r = densityMeasure n ρ := gaussianSmoothingDensity_law n ν _ _ hb
  rw [hμ]
  have hK : (∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ x) ∂densityMeasure n ρ) =
      ∫ x, ρ x * matrixHilbertSchmidtSq (densityLogHessian n ρ x) :=
    density_integral_eq n ρ (gaussianSmoothingDensity_continuous n ν _ _)
      (fun x => (gaussianSmoothingDensity_pos n ν _ _ hb x).le) _
  have hJ : (∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 ∂densityMeasure n ρ) =
      ∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ρ x := by
    rw [density_integral_eq n ρ (gaussianSmoothingDensity_continuous n ν _ _)
      (fun x => (gaussianSmoothingDensity_pos n ν _ _ hb x).le)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _
  rw [hK, hJ] at h
  exact h

theorem ou_relative_fisher_dissipation_integrated (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
      gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
    let I : ℝ → ℝ := fun r => (relativeFisherMeasure n (ouInitialLaw n ν r)).toReal
    let K : ℝ → ℝ := fun r => ∫ x, ∑ i : Fin n,
      ‖gradient (fun y => gaussianRelativeScore n (ρ r) y i) x‖ ^ 2 ∂ouInitialLaw n ν r
    (∀ r : ℝ, 0 < r → relativeFisherMeasure n (ouInitialLaw n ν r) ≠ (∞ : ℝ≥0∞)) ∧
    IntervalIntegrable I volume s t ∧ IntervalIntegrable K volume s t ∧
      I t - I s = ∫ r in s..t, -2 * I r - 2 * K r := by
  let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
    gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
  let J : ℝ → ℝ := fun r => ∫ x, ‖gradient (fun y => Real.log (ρ r y)) x‖ ^ 2 * ρ r x
  let H : ℝ → ℝ := fun r => ∫ x, ρ r x * matrixHilbertSchmidtSq (densityLogHessian n (ρ r) x)
  let I : ℝ → ℝ := fun r => (relativeFisherMeasure n (ouInitialLaw n ν r)).toReal
  let K : ℝ → ℝ := fun r => ∫ x, ∑ i : Fin n,
    ‖gradient (fun y => gaussianRelativeScore n (ρ r) y i) x‖ ^ 2 ∂ouInitialLaw n ν r
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
    memLp_piLp_iff.mpr (isotropic_coordinate_memLp n ν hcov)
  have hU : Integrable (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) ν := hX.integrable (by norm_num)
  have h : IntervalIntegrable J volume s t ∧ IntervalIntegrable H volume s t ∧
      J t - J s = ∫ r in s..t, 2 * J r - 2 * H r :=
    ou_ordinary_fisher_dissipation_integrated n ν hU s t hs hst
  have hIeq (r : ℝ) (hr : 0 < r) : I r = J r - n := (ou_isotropic_relativeFisher_toReal n ν hmean hcov r hr).2
  have hKeq (r : ℝ) (hr : 0 < r) : K r = H r - 2 * J r + n := ou_relative_hessian_energy_identity n ν r hr
  have hAEI : (fun r => J r - n) =ᵐ[volume.restrict (Ι s t)] I := by
    rw [uIoc_of_le hst]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hIeq r (hs.trans hr.1)).symm
  have hAEK : (fun r => H r - 2 * J r + n) =ᵐ[volume.restrict (Ι s t)] K := by
    rw [uIoc_of_le hst]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hKeq r (hs.trans hr.1)).symm
  refine ⟨fun r hr => (ou_isotropic_relativeFisher_toReal n ν hmean hcov r hr).1,
    (h.1.sub intervalIntegrable_const).congr_ae hAEI,
    ((h.2.1.sub (h.1.const_mul 2)).add intervalIntegrable_const).congr_ae hAEK, ?_⟩
  change I t - I s = ∫ r in s..t, -2 * I r - 2 * K r
  rw [hIeq t (hs.trans_le hst), hIeq s hs]
  have hends : (J t - n) - (J s - n) = J t - J s := by ring
  rw [hends, h.2.2]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le hst]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [hIeq r (hs.trans hr.1), hKeq r (hs.trans hr.1)]
  ring

theorem ou_relative_fisher_ae_hasDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
      gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
    let I : ℝ → ℝ := fun r => (relativeFisherMeasure n (ouInitialLaw n ν r)).toReal
    let K : ℝ → ℝ := fun r => ∫ x, ∑ i : Fin n,
      ‖gradient (fun y => gaussianRelativeScore n (ρ r) y i) x‖ ^ 2 ∂ouInitialLaw n ν r
    ∀ᵐ r ∂volume, r ∈ Ioo s t → HasDerivAt I (-2 * I r - 2 * K r) r := by
  apply positive_time_integrated_identity_ae_hasDerivAt _ _ ?_ ?_ s t hs hst
  · intro a b ha hab
    have h := ou_relative_fisher_dissipation_integrated n ν hmean hcov a b ha hab
    exact (h.2.1.const_mul (-2)).sub (h.2.2.1.const_mul 2)
  · intro a b ha hab
    exact (ou_relative_fisher_dissipation_integrated n ν hmean hcov a b ha hab).2.2.2

end AffineFKProof
