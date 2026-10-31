module

public import AffineFK.LogConcaveRepresentative
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Genuine log-concave representatives from strong Lebesgue L2 convergence

Mathlib's convergence-in-measure subsequence theorem supplies the actual
AE pointwise limit. Nonnegativity and the exact square mass are derived
from that convergence and the normalized L2 limit. The selected pointwise
liminf then supplies a finite measurable log-concave representative.
Pointwise symmetry is retained from the actual approximants. No AE
convergence or log-concave-measure equivalence is an input to the result.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology RealInnerProductSpace

theorem logConcave_representative_of_L2_tendsto (n : ℕ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ k, Measurable (f k))
    (hfLp : ∀ k, MemLp (f k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hfnn : ∀ k, ∀ᵐ x ∂volume, 0 ≤ f k x)
    (hlc : ∀ k, LogConcaveDensity (fun x => ENNReal.ofReal (f k x)))
    (ψ : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hψnorm : ‖ψ‖ = 1)
    (hlim : Tendsto (fun k => (hfLp k).toLp (f k)) atTop (𝓝 ψ)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Measurable (logConcaveLiminfRepresentative (fun k x => ENNReal.ofReal (f (ns k) x))) ∧
      (∀ x, 0 ≤ logConcaveLiminfRepresentative (fun k y => ENNReal.ofReal (f (ns k) y)) x) ∧
      LogConcaveDensity (fun x => ENNReal.ofReal
        (logConcaveLiminfRepresentative (fun k y => ENNReal.ofReal (f (ns k) y)) x)) ∧
      logConcaveLiminfRepresentative (fun k x => ENNReal.ofReal (f (ns k) x)) =ᵐ[volume] ψ := by
  obtain ⟨ns, hns, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ x ∂volume, ∀ k, (hfLp k).toLp (f k) x = f k x :=
    ae_all_iff.mpr fun k => (hfLp k).coeFn_toLp
  have hnn : ∀ᵐ x ∂volume, ∀ k, 0 ≤ f k x := ae_all_iff.mpr hfnn
  have hreal : ∀ᵐ x ∂volume,
      Tendsto (fun k => f (ns k) x) atTop (𝓝 (ψ x)) := by
    filter_upwards [hAE, hcoe] with x hx heq
    exact hx.congr' (Eventually.of_forall fun k => heq (ns k))
  have hψnonneg : ∀ᵐ x ∂volume, 0 ≤ ψ x := by
    filter_upwards [hreal, hnn] with x hx hn
    exact ge_of_tendsto' hx (fun k => hn (ns k))
  have hnorm : ‖ψ‖^2 = ∫ x, ‖ψ x‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hmassreal : (∫ x, (ψ x)^2) = 1 := by
    have h := hnorm.symm
    rw [hψnorm] at h
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using h
  have hi : Integrable (fun x => (ψ x)^2) volume :=
    (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable ψ)).mp (Lp.memLp ψ)
  have hmass : (∫⁻ x, (ENNReal.ofReal (ψ x))^2) = 1 := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal ((ψ x)^2) := by
        apply lintegral_congr_ae
        filter_upwards [hψnonneg] with x hx
        exact (ENNReal.ofReal_pow hx 2).symm
      _ = ENNReal.ofReal (∫ x, (ψ x)^2) :=
        (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _)).symm
      _ = 1 := by rw [hmassreal]; simp
  have hENN : ∀ᵐ x ∂volume, Tendsto
      (fun k => ENNReal.ofReal (f (ns k) x)) atTop (𝓝 (ENNReal.ofReal (ψ x))) :=
    hreal.mono fun x hx => (ENNReal.continuous_ofReal.tendsto _).comp hx
  exact ⟨ns, hns, logConcave_real_representative_of_ae_tendsto n
    (fun k x => ENNReal.ofReal (f (ns k) x))
    (fun k => (hf (ns k)).ennreal_ofReal) (fun k => hlc (ns k)) ψ hψnonneg hmass hENN⟩

theorem exists_even_logConcave_representative_of_L2_tendsto (n : ℕ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ k, Measurable (f k))
    (hfLp : ∀ k, MemLp (f k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hfnn : ∀ k, ∀ᵐ x ∂volume, 0 ≤ f k x)
    (hlc : ∀ k, LogConcaveDensity (fun x => ENNReal.ofReal (f k x)))
    (heven : ∀ k x, f k (-x) = f k x)
    (ψ : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hψnorm : ‖ψ‖ = 1)
    (hlim : Tendsto (fun k => (hfLp k).toLp (f k)) atTop (𝓝 ψ)) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∀ x, g (-x) = g x) ∧
      LogConcaveDensity (fun x => ENNReal.ofReal (g x)) ∧ g =ᵐ[volume] ψ := by
  obtain ⟨ns, _hns, hm, hn, hLC, hAE⟩ :=
    logConcave_representative_of_L2_tendsto n f hf hfLp hfnn hlc ψ hψnorm hlim
  refine ⟨logConcaveLiminfRepresentative (fun k x => ENNReal.ofReal (f (ns k) x)),
    hm, hn, ?_, hLC, hAE⟩
  intro x
  exact logConcaveLiminfRepresentative_even
    (fun k (y : EuclideanSpace ℝ (Fin n)) => ENNReal.ofReal (f (ns k) y))
    (fun k (y : EuclideanSpace ℝ (Fin n)) => congrArg ENNReal.ofReal (heven (ns k) y)) x

end AffineFKProof
