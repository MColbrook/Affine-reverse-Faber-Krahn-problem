module

public import AffineFK.GaussianEntropyCalculusTimeIntegration

/-!
# The actual time-integrated compact nonlinear OU identity

Time integrability is proved from local kernel domination and compactness,
then the genuine nonlinear score-flux derivative is integrated. Neither
integrability of this time dissipation nor the integrated identity is a
premise. The spatial and scalar cutoff limits remain separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter Set
open scoped Distributions RealInnerProductSpace Topology Interval ContDiff

theorem ou_compact_nonlinear_dissipation_integrated (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (ψ g g' : ℝ → ℝ)
    (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (g r) r)
    (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (hg' : ∀ r : ℝ, 0 < r → HasDerivAt g (g' r) r)
    (hgm : Measurable g) (B : ℝ) (hB : 0 ≤ B)
    (hgb : ∀ r : ℝ, 0 < r → ‖g r‖ ≤ B)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let D := fun r : ℝ =>
      let a := Real.exp (-r)
      let b := Real.sqrt (1 - Real.exp (-2 * r))
      let q := gaussianSmoothingRelativeDensity n ν a b
      let score := gaussianSmoothingScore n ν a b
      ∫ x, g (q x) * ⟪score x, gradient φ x⟫ + φ x * g' (q x) * q x * ‖score x‖ ^ 2
        ∂densityMeasure n (gaussianSmoothingDensity n ν a b)
    let F := fun r : ℝ => ∫ x : EuclideanSpace ℝ (Fin n), φ x *
      (standardGaussianDensity n x * ψ (gaussianSmoothingDensity n ν (Real.exp (-r))
        (Real.sqrt (1 - Real.exp (-2 * r))) x / standardGaussianDensity n x))
    IntervalIntegrable D volume s t ∧ F s - F t = ∫ r in s..t, D r := by
  let E := EuclideanSpace ℝ (Fin n)
  let q : ℝ → E → ℝ := fun r => gaussianSmoothingRelativeDensity n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r)))
  let score : ℝ → E → E := fun r => gaussianSmoothingScore n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r)))
  let μ : ℝ → Measure E := fun r => densityMeasure n (gaussianSmoothingDensity n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r))))
  let F : ℝ → ℝ := fun r => ∫ x : E, φ x * (standardGaussianDensity n x * ψ (q r x))
  let D : ℝ → ℝ := fun r => ∫ x, g (q r x) * ⟪score r x, gradient φ x⟫ +
    φ x * g' (q r x) * q r x * ‖score r x‖ ^ 2 ∂μ r
  let A : ℝ → ℝ := fun r => ∫ x : E, φ x * g (q r x) * ouDensityTimeDerivative n ν r x
  have hTime : IntervalIntegrable A volume s t ∧ (∫ r in s..t, A r) = F t - F s :=
    ou_compact_entropy_time_integral n ν hU ψ g hψ hgm B hB hgb φ s t hs hst
  have hEq (r : ℝ) (hr : 0 < r) : A r = -D r :=
    ((ou_compact_entropy_chain_rule n ν hU ψ g hψ hgm B hB hgb φ r hr).2).unique
      (ou_compact_nonlinear_dissipation n ν hU ψ g g' hψ hg hg' hgm B hB hgb φ r hr).2
  have hAE : A =ᵐ[volume.restrict (Ι s t)] (fun r => -D r) := by
    rw [uIoc_of_le hst]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hEq r (hs.trans hr.1)
  have hDi : IntervalIntegrable (fun r => -D r) volume s t := hTime.1.congr_ae hAE
  have hI := intervalIntegral.integral_congr_ae_restrict hAE
  have hTI := hTime.2
  rw [hI, intervalIntegral.integral_neg] at hTI
  refine ⟨?_, ?_⟩
  · change IntervalIntegrable D volume s t
    convert! hDi.neg using 1
    funext r
    simp only [Pi.neg_apply, neg_neg]
  · change F s - F t = ∫ r in s..t, D r
    linarith

end AffineFKProof
