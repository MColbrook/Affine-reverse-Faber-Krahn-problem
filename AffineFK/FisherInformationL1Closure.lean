module

public import AffineFK.FisherInformation
public import AffineFK.OrdinaryWeakScoreSobolevLimit

/-!
# Fisher sublevels are closed under L1 convergence of probability densities

The actual square roots converge strongly in L2. The genuine completed
H1 graph and the proved Hilbert bounded-preimage theorem supply a limit
with the same energy bound. No lower-semicontinuity premise is used.
The reused Mathlib integration, Riesz and Banach--Alaoglu proofs retain
the attribution in the imported source modules.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter
open scoped Topology ENNReal Classical

theorem probability_density_sqrt_l2_norm_sq (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hf : f =ᵐ[volume] fun x => Real.sqrt (ρ x)) : ‖f‖ ^ 2 = 1 := by
  have hlin : (∫⁻ x, ENNReal.ofReal (ρ x) ∂volume) = 1 := by
    have h := measure_univ (μ := densityMeasure n ρ)
    simpa only [densityMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using h
  have hmass : (∫ x, ρ x) = 1 := by
    have h := ofReal_integral_eq_lintegral_ofReal hρ (Eventually.of_forall hρ0)
    rw [hlin] at h
    have ht := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_ofReal (integral_nonneg hρ0), ENNReal.toReal_one] using ht
  rw [l2_norm_sq_integral]
  calc
    _ = ∫ x, ρ x := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
      simp only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hρ0 x)]
    _ = 1 := hmass

theorem fisherInformation_le_of_density_L1_limit (n : ℕ)
    (ρk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρk0 : ∀ k x, 0 ≤ ρk k x)
    (hρ : Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hρk : ∀ k, Integrable (ρk k) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n ρ)]
    [∀ k, IsProbabilityMeasure (densityMeasure n (ρk k))]
    (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ k, fisherInformation n (ρk k) ≤ ENNReal.ofReal M)
    (hL1 : Tendsto (fun k => ∫ x, ‖ρk k x - ρ x‖) atTop (𝓝 0)) :
    fisherInformation n ρ ≤ ENNReal.ofReal M := by
  have hd (k : ℕ) : sqrtDensitySobolev n (ρk k) := by
    apply (fisherInformation_ne_top_iff n (ρk k)).mp
    intro ht
    have h := hF k
    rw [ht] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
  let v : ℕ → unweightedSobolevGraph n := fun k => (hd k).choose
  have hv (k : ℕ) : (unweightedValue n (v k) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρk k x) := (hd k).choose_spec
  have hvalue (k : ℕ) : ‖unweightedValue n (v k)‖ ^ 2 = 1 :=
    probability_density_sqrt_l2_norm_sq n (ρk k) (hρk0 k) (hρk k) _ (hv k)
  have hgradient (k : ℕ) : 4 * ‖unweightedGradient n (v k)‖ ^ 2 ≤ M := by
    have h := hF k
    rw [fisherInformation_eq_graph n (ρk k) (v k) (hv k)] at h
    have hb := (ENNReal.ofReal_le_ofReal_iff hM).mp h
    rwa [← l2_norm_sq_integral] at hb
  have hfLp := densityApproximation_sqrt_memLp volume ρ hm (Eventually.of_forall hρ0) hρ
  let f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hfLp.toLp (fun x => Real.sqrt (ρ x))
  have hf : f =ᵐ[volume] fun x => Real.sqrt (ρ x) := hfLp.coeFn_toLp
  have hlimit : Tendsto (fun k => unweightedValue n (v k)) atTop (𝓝 f) :=
    densityApproximation_sqrt_L2_tendsto volume ρk ρ
      (fun k => Eventually.of_forall (hρk0 k)) (Eventually.of_forall hρ0)
      hρk hρ _ f hv hf hL1
  obtain ⟨w, hw, hbound⟩ := ordinaryWeakScore_graph_limit n v f M hM
    (probability_density_sqrt_l2_norm_sq n ρ hρ0 hρ f hf) hvalue hgradient hlimit
  have hwAE : (unweightedValue n w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x) := by rw [hw]; exact hf
  rw [fisherInformation_eq_graph n ρ w hwAE]
  apply ENNReal.ofReal_le_ofReal
  rwa [l2_norm_sq_integral] at hbound

end AffineFKProof
