module

public import AffineFK.OrdinaryWeakScoreSobolevRegularization
public import AffineFK.OrdinaryWeakScoreSobolevLimit

/-!
# A genuine ordinary weak-score to square-root H1 converse

Actual Gaussian regularization gives positive smooth densities, genuine
square-root H1 elements and a uniform gradient-energy bound. Proved
Lebesgue L1 convergence of the actual densities yields strong L2
convergence of their square roots. The actual Hilbert graph compactness
argument then supplies the original density's H1 square root, with the
claimed energy bound. No approximation, compactness or output conclusion
is assumed, and no moment condition is imposed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped Distributions Topology RealInnerProductSpace

theorem ordinaryWeakScore_sqrt_sobolev (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ : Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hs : MemLp s 2 (densityMeasure n ρ))
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, s x i * φ x ∂densityMeasure n ρ) =
        -(∫ x, partialTest n i φ x ∂densityMeasure n ρ)) :
    ∃ v : unweightedSobolevGraph n,
      (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun x => Real.sqrt (ρ x)) ∧
      4 * (∫ x, ‖unweightedGradient n v x‖ ^ 2) ≤
        ∫ x, ‖s x‖ ^ 2 ∂densityMeasure n ρ := by
  let ν := densityMeasure n ρ
  let b : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  have hb (k : ℕ) : 0 < b k := by dsimp [b]; positivity
  let ρk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k => gaussianSmoothingDensity n ν 1 (b k)
  have hprob (k : ℕ) : IsProbabilityMeasure (densityMeasure n (ρk k)) := by
    have hlaw := gaussianSmoothingDensity_law n ν 1 (b k) (hb k)
    change IsProbabilityMeasure (densityMeasure n (gaussianSmoothingDensity n ν 1 (b k)))
    rw [← hlaw]
    infer_instance
  have hρk0 (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ ρk k x :=
    (gaussianSmoothingDensity_pos n ν 1 (b k) (hb k) x).le
  have hρk (k : ℕ) : Integrable (ρk k) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    let := hprob k
    exact ordinaryWeakScore_smooth_density_integrable n (ρk k)
      (gaussianSmoothingDensity_smooth n ν 1 (b k))
      (gaussianSmoothingDensity_pos n ν 1 (b k) (hb k))
  have hregular (k : ℕ) := ordinaryWeakScore_gaussian_regularization n ν s hs hweak (b k) (hb k)
  choose v hv hvalue hgradient using hregular
  have hfLp := densityApproximation_sqrt_memLp volume ρ hm
    (Eventually.of_forall hρ0) hρ
  let f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hfLp.toLp (fun x => Real.sqrt (ρ x))
  have hfAE : f =ᵐ[volume] fun x => Real.sqrt (ρ x) := hfLp.coeFn_toLp
  have hmass : (∫ x, ρ x) = 1 := by
    have hlin : (∫⁻ x, ENNReal.ofReal (ρ x) ∂volume) = 1 := by
      have h := measure_univ (μ := ν)
      simpa only [ν, densityMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using h
    have h := ofReal_integral_eq_lintegral_ofReal hρ (Eventually.of_forall hρ0)
    rw [hlin] at h
    have ht := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_ofReal (integral_nonneg hρ0), ENNReal.toReal_one] using ht
  have hfNorm : ‖f‖ ^ 2 = 1 := by
    rw [l2_norm_sq_integral]
    calc
      _ = ∫ x, ρ x := by
        apply integral_congr_ae
        filter_upwards [hfAE] with x hx
        rw [hx]
        simp only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hρ0 x)]
      _ = 1 := hmass
  have hbLimit : Tendsto b atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_inverse_succ, Eventually.of_forall hb⟩
  have hL1 : Tendsto (fun k => ∫ x, ‖ρk k x - ρ x‖) atTop (𝓝 0) :=
    (densityApproximation_gaussian_density_L1_tendsto n ρ hm hρ0 hρ).comp hbLimit
  have hL2 : Tendsto (fun k => unweightedValue n (v k)) atTop (𝓝 f) :=
    densityApproximation_sqrt_L2_tendsto volume ρk ρ
      (fun k => Eventually.of_forall (hρk0 k)) (Eventually.of_forall hρ0) hρk hρ
      (fun k => unweightedValue n (v k)) f hv hfAE hL1
  obtain ⟨w, hw, hbound⟩ := ordinaryWeakScore_graph_limit n v f
    (∫ x, ‖s x‖ ^ 2 ∂ν) (integral_nonneg fun x => sq_nonneg _) hfNorm hvalue hgradient hL2
  refine ⟨w, ?_, ?_⟩
  · rw [hw]
    exact hfAE
  · rwa [l2_norm_sq_integral] at hbound

end AffineFKProof
