module

public import AffineFK.FiniteSobolevDensityScore
public import AffineFK.OUScoreInformationBounds

/-!
# OU score bounds on the original square-root Sobolev domain

The initial value is the actual nonnegative square root of the density in
the unweighted H1 completion. The original score equation is derived from
that Sobolev hypothesis. No smoothness of the initial density or assumed
weak score equation occurs. The output is the actual logarithmic score of
the positive smooth Gaussian-relative density of the actual OU law.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem finiteSobolev_OU_score_bound (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x))
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ))
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    MemLp (gaussianSmoothingScore n (densityMeasure n ρ) (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t)))) 2
      (((densityMeasure n ρ).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ∧
    (∫ x, ‖gaussianSmoothingScore n (densityMeasure n ρ) (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t))) x‖ ^ 2
      ∂((densityMeasure n ρ).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ≤
      Real.exp (-2 * t) *
        (∫ x, ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2) := by
  obtain ⟨s, _, hs, _, hI, henergy, hweak⟩ :=
    finiteSobolev_density_relative_score n ρ hρ0 v hv hsecond
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      2 (densityMeasure n ρ) :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr hsecond
  have hxi (i : Fin n) : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i)
      2 (densityMeasure n ρ) := hX.eval_piLp i
  have hout := OU_firstOrder_relative_score_information_bound n (densityMeasure n ρ) hxi
    s hs (fun F => (hweak F).2.2) t ht
  exact ⟨hI, hout.1, hout.2.trans (mul_le_mul_of_nonneg_left henergy (Real.exp_pos _).le)⟩

theorem finiteSobolev_OU_two_score_bounds (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x))
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ))
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 (densityMeasure n ρ))
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ) =
        ∫ x, vectorHessianContraction n T F x ∂densityMeasure n ρ)
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    MemLp (gaussianSmoothingScore n (densityMeasure n ρ) (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t)))) 2
      (((densityMeasure n ρ).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ∧
    (∫ x, ‖gaussianSmoothingScore n (densityMeasure n ρ) (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t))) x‖ ^ 2
      ∂((densityMeasure n ρ).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ≤
      min (Real.exp (-2 * t) *
        (∫ x, ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2))
        ((2 * Real.exp (-6 * t) / (1 - Real.exp (-2 * t)) ^ 2) *
          (∫ x, ‖T x‖ ^ 2 ∂densityMeasure n ρ)) := by
  have hfirst := finiteSobolev_OU_score_bound n ρ hρ0 v hv hsecond t ht
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      2 (densityMeasure n ρ) :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr hsecond
  have hxi (i : Fin n) : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i)
      2 (densityMeasure n ρ) := hX.eval_piLp i
  have hsecondBound := OU_stein_relative_score_information_bound n (densityMeasure n ρ)
    hxi T hT hidentity t ht
  exact ⟨hfirst.1, hfirst.2.1, le_min hfirst.2.2 hsecondBound.2⟩

end AffineFKProof
