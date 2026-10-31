module

public import AffineFK.OrdinaryWeakScoreSobolevSmooth
public import AffineFK.DensityApproximationL1Gaussian
public import AffineFK.OrdinaryFisherConvolutionComponents

/-!
# Actual Gaussian regularization of an ordinary weak score

The independently proved conditional convolution score is transported to
the actual positive Gaussian-mixture density. Compact-test uniqueness
identifies its true logarithmic score and proves genuine square-root H1
membership and the uniform energy bound. No Sobolev conclusion or desired
regularized score equation is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff

theorem ordinaryWeakScore_gaussian_regularization (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, s x i * φ x ∂ν) = -(∫ x, partialTest n i φ x ∂ν))
    (b : ℝ) (hb : 0 < b) :
    ∃ v : unweightedSobolevGraph n,
      (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun x => Real.sqrt (gaussianSmoothingDensity n ν 1 b x)) ∧
      ‖unweightedValue n v‖ ^ 2 = 1 ∧
      4 * ‖unweightedGradient n v‖ ^ 2 ≤ ∫ x, ‖s x‖ ^ 2 ∂ν := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  let η := γ.map (fun g => b • g)
  let ρ := gaussianSmoothingDensity n ν 1 b
  have hρ : ContDiff ℝ ∞ ρ := gaussianSmoothingDensity_smooth n ν 1 b
  have hρpos : ∀ x, 0 < ρ x := gaussianSmoothingDensity_pos n ν 1 b hb
  have hlaw : (η.prod ν).map (fun p => p.1 + p.2) = densityMeasure n ρ := by
    have h := (densityApproximation_gaussian_sum_law n ν b).trans
      (show (ν.prod γ).map (fun p => p.1 + b • p.2) = densityMeasure n ρ by
        simpa only [one_smul] using gaussianSmoothingDensity_law n ν 1 b hb)
    exact h
  let : IsProbabilityMeasure (densityMeasure n ρ) := by
    rw [← hlaw]
    infer_instance
  obtain ⟨r, _hr, hrLp, _hrep, hbound, hwr⟩ :=
    ordinaryFisher_convolution_conditional_score n η ν s hs hweak
  rw [hlaw] at hrLp hbound hwr
  have hc := ordinaryFisher_weak_vector_components n (densityMeasure n ρ) r hwr
  obtain ⟨v, hv, _hgv, henergy⟩ := ordinaryWeakScore_smooth_sqrt_graph_of_weak_score n ρ hρ hρpos
    r hrLp (fun i φ => (hc i φ).2.2)
  refine ⟨v, hv, ?_, ?_⟩
  · have hmass : (∫ x, ρ x) = 1 := by
      have h := density_integral_eq n ρ hρ.continuous (fun x => (hρpos x).le) (fun _ => (1 : ℝ))
      simpa only [integral_const, probReal_univ, one_smul, mul_one] using h.symm
    rw [l2_norm_sq_integral]
    calc
      _ = ∫ x, ρ x := by
        apply integral_congr_ae
        filter_upwards [hv] with x hx
        rw [hx]
        simp only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hρpos x).le]
      _ = 1 := hmass
  · rw [l2_norm_sq_integral, henergy]
    exact hbound

end AffineFKProof
