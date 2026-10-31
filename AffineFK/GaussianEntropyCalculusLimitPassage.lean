module

public import AffineFK.GaussianEntropyCalculusTimeDissipation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A guarded limit passage for integrated dissipation identities

Every measurable/dominating/pointwise-convergence premise is explicit.
Integrability of the limiting time dissipation is concluded, not assumed.
The OU application must discharge these premises using its actual cutoff
identities and score bounds; this general lemma alone is not de Bruijn.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter Set
open scoped Topology Interval

theorem entropy_integrated_cutoff_limit
    (F : ℕ → ℝ → ℝ) (D : ℕ → ℝ → ℝ) (f d : ℝ → ℝ)
    (s t : ℝ) (hst : s ≤ t)
    (hFTC : ∀ k : ℕ, F k s - F k t = ∫ r in s..t, D k r)
    (hFs : Tendsto (fun k => F k s) atTop (𝓝 (f s)))
    (hFt : Tendsto (fun k => F k t) atTop (𝓝 (f t)))
    (hDm : ∀ k, AEStronglyMeasurable (D k) (volume.restrict (Ioc s t)))
    (J : ℝ → ℝ) (hJ : IntegrableOn J (Ioc s t) volume)
    (hbound : ∀ k, ∀ᵐ r ∂volume.restrict (Ioc s t), ‖D k r‖ ≤ J r)
    (hpoint : ∀ᵐ r ∂volume.restrict (Ioc s t), Tendsto (fun k => D k r) atTop (𝓝 (d r))) :
    IntervalIntegrable d volume s t ∧ f s - f t = ∫ r in s..t, d r := by
  have hdm : AEStronglyMeasurable d (volume.restrict (Ioc s t)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hDm hpoint
  have hdBound : ∀ᵐ r ∂volume.restrict (Ioc s t), ‖d r‖ ≤ J r := by
    filter_upwards [ae_all_iff.mpr hbound, hpoint] with r hr hp
    exact le_of_tendsto hp.norm (Filter.Eventually.of_forall hr)
  have hdi : IntegrableOn d (Ioc s t) volume := hJ.mono' hdm hdBound
  have hlim := tendsto_integral_of_dominated_convergence J hDm hJ hbound hpoint
  have hlim' : Tendsto (fun k : ℕ => ∫ r in s..t, D k r) atTop (𝓝 (∫ r in s..t, d r)) := by
    simpa only [intervalIntegral.integral_of_le hst] using hlim
  have hends : Tendsto (fun k : ℕ => ∫ r in s..t, D k r) atTop (𝓝 (f s - f t)) := by
    simpa only [← hFTC] using hFs.sub hFt
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr hdi,
    (tendsto_nhds_unique hlim' hends).symm⟩

end AffineFKProof
