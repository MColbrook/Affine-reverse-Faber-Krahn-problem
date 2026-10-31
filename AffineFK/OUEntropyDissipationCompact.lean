module

public import AffineFK.GaussianEntropyCalculusTimeDissipation
public import AffineFK.EntropyTruncationBounds

/-!
# Genuine entropy truncations in the integrated compact OU identity

The scalar functions are the explicitly defined logarithmic truncations;
their calculus and boundedness are proved in EntropyTruncation and
EntropyTruncationBounds. The conclusion is the actual compact-cutoff
identity, including time integrability, without an assumed entropy chain
rule. The spatial/scalar limits to full KL are separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace Topology Interval ContDiff

theorem ou_truncated_compact_entropy_dissipation (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (ε L : ℝ) (hε : 0 < ε) (hεL : ε ≤ L)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let D := fun r : ℝ =>
      let a := Real.exp (-r)
      let b := Real.sqrt (1 - Real.exp (-2 * r))
      let q := gaussianSmoothingRelativeDensity n ν a b
      let score := gaussianSmoothingScore n ν a b
      ∫ x, entropyTruncationDeriv ε L (q x) * ⟪score x, gradient φ x⟫ +
        φ x * ((q x + ε)⁻¹ - (q x + L)⁻¹) * q x * ‖score x‖ ^ 2
        ∂densityMeasure n (gaussianSmoothingDensity n ν a b)
    let F := fun r : ℝ => ∫ x : EuclideanSpace ℝ (Fin n), φ x *
      (standardGaussianDensity n x * entropyTruncation ε L
        (gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r))) x /
          standardGaussianDensity n x))
    IntervalIntegrable D volume s t ∧ F s - F t = ∫ r in s..t, D r := by
  have hL : 0 < L := hε.trans_le hεL
  obtain ⟨B, hB, hBb⟩ := entropyTruncationDeriv_uniform_bound ε L hε hεL
  have hsm (r : ℝ) (hr : 0 < r) : ContDiffAt ℝ ∞ (entropyTruncationDeriv ε L) r := by
    unfold entropyTruncationDeriv
    fun_prop (disch := positivity)
  have hmm : Measurable (entropyTruncationDeriv ε L) := by
    unfold entropyTruncationDeriv
    fun_prop
  exact ou_compact_nonlinear_dissipation_integrated n ν hU
    (entropyTruncation ε L) (entropyTruncationDeriv ε L)
    (fun r => (r + ε)⁻¹ - (r + L)⁻¹)
    (fun r hr => entropyTruncation_hasDerivAt ε L r hε hL hr.le) hsm
    (fun r hr => entropyTruncationDeriv_hasDerivAt ε L r hε hL hr.le) hmm B hB
    (fun r hr => by simpa only [Real.norm_eq_abs] using hBb r hr.le) φ s t hs hst

end AffineFKProof
