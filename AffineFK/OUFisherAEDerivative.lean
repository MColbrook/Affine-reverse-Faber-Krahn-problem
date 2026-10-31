module

public import AffineFK.OUFisherDissipation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The actual ordinary Fisher derivative almost everywhere in positive time

Yizheng Zhu's Mathlib interval Lebesgue differentiation theorem converts
the proved integrated identity into a genuine almost-everywhere temporal
derivative. Neither a pointwise Fisher derivative nor continuity of the
integrated Hessian energy is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter Set
open scoped Topology Interval

theorem positive_time_integrated_identity_ae_hasDerivAt
    (J D : ℝ → ℝ)
    (hi : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable D volume a b)
    (hFTC : ∀ a b : ℝ, 0 < a → a ≤ b → J b - J a = ∫ r in a..b, D r)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    ∀ᵐ r ∂volume, r ∈ Ioo s t → HasDerivAt J (D r) r := by
  filter_upwards [(hi s t hs hst).ae_hasDerivAt_integral] with r hr
  intro hrmem
  have hrcc : r ∈ uIcc s t := by
    rw [uIcc_of_le hst]
    exact ⟨hrmem.1.le, hrmem.2.le⟩
  have hscc : s ∈ uIcc s t := by
    rw [uIcc_of_le hst]
    exact ⟨le_rfl, hst⟩
  have h := (hr hrcc s hscc).const_add (J s)
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hrmem.1] with u hu
  have hEq := hFTC s u hs hu.le
  linarith

theorem ou_ordinary_fisher_ae_hasDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
      gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
    let J : ℝ → ℝ := fun r => ∫ x, ‖gradient (fun y => Real.log (ρ r y)) x‖ ^ 2 * ρ r x
    let K : ℝ → ℝ := fun r => ∫ x, ρ r x * matrixHilbertSchmidtSq (densityLogHessian n (ρ r) x)
    ∀ᵐ r ∂volume, r ∈ Ioo s t → HasDerivAt J (2 * J r - 2 * K r) r := by
  apply positive_time_integrated_identity_ae_hasDerivAt _ _ ?_ ?_ s t hs hst
  · intro a b ha hab
    have h := ou_ordinary_fisher_dissipation_integrated n ν hU a b ha hab
    exact (h.1.const_mul 2).sub (h.2.1.const_mul 2)
  · intro a b ha hab
    exact (ou_ordinary_fisher_dissipation_integrated n ν hU a b ha hab).2.2

end AffineFKProof
