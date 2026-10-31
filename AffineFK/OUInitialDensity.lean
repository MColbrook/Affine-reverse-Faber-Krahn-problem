module

public import AffineFK.OUInitialLimit
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# L1 approximation by the actual Gaussian OU coupling

Mathlib's continuity of Lp composition by continuous measure-preserving
maps (Yury Kudryashov), and its conditional Radon--Nikodym and conditional
expectation contraction results (Rémy Degenne and contributors), are used
with their actual measures. Relative entropy finiteness is not an input.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

def ouInitialClampMap (n : ℕ) (t : ℝ) :
    C(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
  ⟨fun p => Real.exp (-max t 0) • p.1 +
      Real.sqrt (1 - Real.exp (-2 * max t 0)) • p.2, by fun_prop⟩

theorem ouInitial_clamp_measurePreserving (n : ℕ) (t : ℝ) :
    MeasurePreserving (ouInitialClampMap n t)
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  refine ⟨(ouInitialClampMap n t).continuous.measurable, ?_⟩
  apply ouInitial_gaussian_affine_invariant
  have he : Real.exp (-2 * max t 0) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := le_max_right t 0
    linarith)
  rw [ou_exponential_power, Real.sq_sqrt (sub_nonneg.mpr he)]
  simp

theorem ouInitial_clamp_continuous (n : ℕ) : Continuous (ouInitialClampMap n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
    Real.exp (-max p.1 0) • p.2.1 + Real.sqrt (1 - Real.exp (-2 * max p.1 0)) • p.2.2)
  fun_prop

theorem ouInitial_pullback_L1_tendsto (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f (stdGaussian (EuclideanSpace ℝ (Fin n)))) :
    Tendsto (fun t : ℝ => ∫ p, ‖f (ouInitialClampMap n t p) - f p.1‖
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) (𝓝 0) (𝓝 0) := by
  let fL := hf.toL1 f
  let g (t : ℝ) := Lp.compMeasurePreserving (ouInitialClampMap n t)
    (ouInitial_clamp_measurePreserving n t) fL
  have hg : Tendsto g (𝓝 (0 : ℝ)) (𝓝 (g 0)) :=
    tendsto_const_nhds.compMeasurePreservingLp
      (ouInitial_clamp_continuous n).continuousAt.tendsto
      (ouInitial_clamp_measurePreserving n) (ouInitial_clamp_measurePreserving n 0) (by simp)
  have hdist := (tendsto_iff_dist_tendsto_zero).mp hg
  convert hdist using 1
  ext t
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  have hgt := (Lp.coeFn_compMeasurePreserving fL (ouInitial_clamp_measurePreserving n t)).trans
    ((ouInitial_clamp_measurePreserving n t).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1)
  have hg0 := (Lp.coeFn_compMeasurePreserving fL (ouInitial_clamp_measurePreserving n 0)).trans
    ((ouInitial_clamp_measurePreserving n 0).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1)
  filter_upwards [hgt, hg0] with p ht h0
  simp only [g, fL] at ht h0 ⊢
  rw [ht, h0]
  simp [ouInitialClampMap, Real.dist_eq, Real.norm_eq_abs]

theorem ouInitial_RN_L1_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ stdGaussian (EuclideanSpace ℝ (Fin n)))
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (∫ x, ‖(((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)).rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal -
        (ν.rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal‖
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ∫ p, ‖(ν.rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) p.1).toReal -
        (ν.rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) (a • p.1 + b • p.2)).toReal‖
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let Γ := γ.prod γ
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (ν.rnDeriv γ x).toReal
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (((ν.prod γ).map W).rnDeriv γ x).toReal
  have hW : Measurable W := by fun_prop
  have hmap : Γ.map W = γ := ouInitial_gaussian_affine_invariant n a b hab
  have hpres : MeasurePreserving W Γ γ := ⟨hW, hmap⟩
  let m := (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W
  let _ : MeasurableSpace (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    Prod.instMeasurableSpace
  have hm : m ≤ (inferInstance : MeasurableSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) := hW.comap_le
  have hf : Integrable f γ := Measure.integrable_toReal_rnDeriv
  have hfm : Measurable f := (Measure.measurable_rnDeriv ν γ).ennreal_toReal
  have hfW : Integrable (fun p => f (W p)) Γ := hpres.integrable_comp_of_integrable hf
  have hfX : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => f p.1) Γ :=
    hf.comp_fst γ
  have hfWm : StronglyMeasurable[m] (fun p => f (W p)) :=
    (hfm.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable
  have hprod : (fun p => ((ν.prod γ).rnDeriv Γ p).toReal) =ᵐ[Γ] (fun p => f p.1) := by
    have h := rnDeriv_measure_compProd_left ν γ (Kernel.const (EuclideanSpace ℝ (Fin n)) γ)
    simp only [Measure.compProd_const] at h
    exact h.fun_comp ENNReal.toReal
  have hCE : (fun p => q (W p)) =ᵐ[Γ] condExp m Γ (fun p => f p.1) := by
    have hacprod : ν.prod γ ≪ Γ := hac.prod (Measure.AbsolutelyContinuous.rfl (μ := γ))
    have h := toReal_rnDeriv_map (μ := ν.prod γ) (ν := Γ) hacprod hW
    rw [hmap] at h
    exact h.trans (condExp_congr_ae hprod)
  have hsub : condExp m Γ (fun p => f p.1 - f (W p)) =ᵐ[Γ]
      (fun p => q (W p) - f (W p)) := by
    have h := condExp_sub hfX hfW m
    rw [condExp_of_stronglyMeasurable (μ := Γ) hm hfWm hfW] at h
    exact h.trans (hCE.symm.sub Filter.EventuallyEq.rfl)
  change (∫ x, ‖q x - f x‖ ∂γ) ≤ ∫ p, ‖f p.1 - f (W p)‖ ∂Γ
  have hqm : Measurable q := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have he := integral_map (μ := Γ) (φ := W) (f := fun x => ‖q x - f x‖)
    hW.aemeasurable ((hqm.sub hfm).norm.aestronglyMeasurable)
  rw [hmap] at he
  rw [he]
  have he2 : (∫ p, ‖condExp m Γ (fun p => f p.1 - f (W p)) p‖ ∂Γ) =
      ∫ p, ‖q (W p) - f (W p)‖ ∂Γ := integral_congr_ae (hsub.fun_comp norm)
  rw [← he2]
  exact integral_norm_condExp_le _

theorem ouInitial_clamped_RN_L1_tendsto (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ stdGaussian (EuclideanSpace ℝ (Fin n))) :
    Tendsto (fun t : ℝ => ∫ x,
      ‖((ouInitialLaw n ν (max t 0)).rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal -
        (ν.rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal‖
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) (𝓝 0) (𝓝 0) := by
  have hright := ouInitial_pullback_L1_tendsto n
    (fun x => (ν.rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal)
    Measure.integrable_toReal_rnDeriv
  apply squeeze_zero (fun t => integral_nonneg (fun x => norm_nonneg _)) _ hright
  intro t
  have hbound := ouInitial_RN_L1_bound n ν hac
    (Real.exp (-max t 0)) (Real.sqrt (1 - Real.exp (-2 * max t 0))) (by
      have he : Real.exp (-2 * max t 0) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have := le_max_right t 0
        linarith)
      rw [ou_exponential_power, Real.sq_sqrt (sub_nonneg.mpr he)]
      simp)
  convert hbound using 1
  · rfl
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => norm_sub_rev _ _

end AffineFKProof
