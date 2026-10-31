module

public import AffineFK.OUInitialDensity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# The initial OU entropy endpoint, including infinite entropy

For an arbitrary probability measure absolutely continuous with respect
to the actual standard Gaussian, the actual RN densities converge in L1.
Subsequence extraction and Fatou for the nonnegative Mathlib klFun give
the entropy lower bound; actual KL data processing gives the upper bound.
No finite entropy or integrable logarithmic density is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped Topology ENNReal

theorem ouInitial_klDiv_tendsto_of_RN_inMeasure
    {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (γ : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (μs : I → Measure X) [∀ i, IsProbabilityMeasure (μs i)]
    (l : Filter I) [NeBot l] [l.IsCountablyGenerated]
    (hac : μ ≪ γ) (hacs : ∀ i, μs i ≪ γ)
    (hRN : TendstoInMeasure γ
      (fun i x => ((μs i).rnDeriv γ x).toReal) l (fun x => (μ.rnDeriv γ x).toReal))
    (hupper : ∀ i, klDiv (μs i) γ ≤ klDiv μ γ) :
    Tendsto (fun i => klDiv (μs i) γ) l (𝓝 (klDiv μ γ)) := by
  let H : I → ℝ≥0∞ := fun i => klDiv (μs i) γ
  obtain ⟨s, hsH, hsl⟩ := exists_seq_tendsto_liminf (f := l) (u := H)
  obtain ⟨j, hj, hAE⟩ := (hRN.comp hsl).exists_seq_tendsto_ae'
  have hlimit : Tendsto (fun k => H (s (j k))) atTop (𝓝 (liminf H l)) := hsH.comp hj
  have hnonnegLimit : ∀ᵐ x ∂γ,
      Tendsto (fun k => ENNReal.ofReal (klFun (((μs (s (j k))).rnDeriv γ x).toReal)))
        atTop (𝓝 (ENNReal.ofReal (klFun ((μ.rnDeriv γ x).toReal)))) :=
    hAE.mono fun x hx =>
      (ENNReal.continuous_ofReal.comp continuous_klFun).continuousAt.tendsto.comp hx
  have hfatou := lintegral_liminf_le' (μ := γ)
    (f := fun k x => ENNReal.ofReal (klFun (((μs (s (j k))).rnDeriv γ x).toReal)))
    (u := atTop) (fun k => by fun_prop)
  have hpoint : (∫⁻ x, (liminf
      (fun k => ENNReal.ofReal (klFun (((μs (s (j k))).rnDeriv γ x).toReal))) atTop) ∂γ) =
      ∫⁻ x, ENNReal.ofReal (klFun ((μ.rnDeriv γ x).toReal)) ∂γ :=
    lintegral_congr_ae (hnonnegLimit.mono fun x hx => hx.liminf_eq)
  rw [hpoint, ← klDiv_eq_lintegral_klFun_of_ac hac] at hfatou
  have hvalues : (fun k => ∫⁻ x,
      ENNReal.ofReal (klFun (((μs (s (j k))).rnDeriv γ x).toReal)) ∂γ) =
      (fun k => H (s (j k))) := by
    funext k
    exact (klDiv_eq_lintegral_klFun_of_ac (hacs _)).symm
  rw [hvalues, hlimit.liminf_eq] at hfatou
  apply tendsto_of_le_liminf_of_limsup_le hfatou
  exact limsup_le_of_le (h := Filter.Eventually.of_forall hupper)

theorem ouInitial_clamped_RN_tendstoInMeasure (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ stdGaussian (EuclideanSpace ℝ (Fin n))) :
    TendstoInMeasure (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (fun t : ℝ => fun x =>
        ((ouInitialLaw n ν (max t 0)).rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal)
      (𝓝 0) (fun x => (ν.rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ℝ≥0∞)) (by norm_num)
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (ouInitial_clamped_RN_L1_tendsto n ν hac)
  convert h using 1
  · ext t
    rw [eLpNorm_one_eq_lintegral_enorm (by fun_prop)]
    exact (ofReal_integral_norm_eq_lintegral_enorm
      (Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv)).symm
  · simp

theorem ouInitial_clamped_law_absolutelyContinuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ stdGaussian (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    ouInitialLaw n ν (max t 0) ≪ stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  have h := (hac.prod (Measure.AbsolutelyContinuous.rfl
    (μ := stdGaussian (EuclideanSpace ℝ (Fin n))))).map
      (show Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Real.exp (-max t 0) • p.1 + Real.sqrt (1 - Real.exp (-2 * max t 0)) • p.2) by fun_prop)
  have hmap := (ouInitial_clamp_measurePreserving n t).map_eq
  exact hmap ▸ h

theorem ouInitial_clamped_entropy_tendsto (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ stdGaussian (EuclideanSpace ℝ (Fin n))) :
    Tendsto (fun t : ℝ => klDiv (ouInitialLaw n ν (max t 0))
      (stdGaussian (EuclideanSpace ℝ (Fin n)))) (𝓝 0)
      (𝓝 (klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))))) := by
  apply ouInitial_klDiv_tendsto_of_RN_inMeasure ν
    (stdGaussian (EuclideanSpace ℝ (Fin n)))
    (fun t : ℝ => ouInitialLaw n ν (max t 0)) (𝓝 0) hac
    (ouInitial_clamped_law_absolutelyContinuous n ν hac)
    (ouInitial_clamped_RN_tendstoInMeasure n ν hac)
  intro t
  exact ouInitial_entropy_contraction n ν (max t 0) (le_max_right _ _)

theorem ouInitial_entropy_tendsto (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ stdGaussian (EuclideanSpace ℝ (Fin n))) :
    Tendsto (fun t : ℝ => klDiv (ouInitialLaw n ν t)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))) (𝓝[>] 0)
      (𝓝 (klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))))) := by
  have h := (ouInitial_clamped_entropy_tendsto n ν hac).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [max_eq_left (le_of_lt ht)]

end AffineFKProof
