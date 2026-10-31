module

public import AffineFK.DirichletGroundstateExistence
public import AffineFK.SobolevFisherIdentityGraph
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Strict positivity of the actual bounded-domain Dirichlet infimum

A normalized minimizer defines a genuine square-density probability.
Its bounded support gives the required coordinate L2 moment. The proved
Sobolev cutoff identity then rules out a zero gradient. No pointwise
regularity, eigenfunction positivity or spectral proxy is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace ENNReal

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem dirichletValue_ae_zero_outside (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hUK : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ K) (ψ : dirichletSobolev n U) :
    ∀ᵐ x ∂volume, x ∉ K → dirichletValue n U ψ x = 0 := by
  obtain ⟨g, hg⟩ := dirichletRellich_value_supported n U K hK hUK ψ
  have hae := Lp.extendByZeroₗᵢ_ae_eq
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hK g
  filter_upwards [hae] with x hx
  intro hxK
  have heq := congrArg (fun f : Lp ℝ 2
    (volume : Measure (EuclideanSpace ℝ (Fin n))) => f x) hg
  exact heq.symm.trans (hx.trans (Set.indicator_of_notMem hxK _))

theorem dirichletValue_coordinate_memLp (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (ψ : dirichletSobolev n U) :
    MemLp (fun x => dirichletValue n U ψ x • x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let K := closure (U : Set (EuclideanSpace ℝ (Fin n)))
  have hK : IsCompact K := hbounded.isCompact_closure
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  have hzero := dirichletValue_ae_zero_outside n U K hK.measurableSet subset_closure ψ
  have hf := Lp.memLp (dirichletValue n U ψ)
  apply (hf.norm.const_mul R).mono'
    (hf.aestronglyMeasurable.smul measurable_id.aestronglyMeasurable)
  filter_upwards [hzero] with x hx
  change ‖dirichletValue n U ψ x • x‖ ≤ R * ‖dirichletValue n U ψ x‖
  by_cases hxK : x ∈ K
  · calc
      ‖dirichletValue n U ψ x • x‖ = ‖dirichletValue n U ψ x‖ * ‖x‖ := norm_smul _ _
      _ ≤ ‖dirichletValue n U ψ x‖ * R :=
        mul_le_mul_of_nonneg_left (hR x hxK) (norm_nonneg _)
      _ = R * ‖dirichletValue n U ψ x‖ := mul_comm _ _
  · rw [hx hxK]
    simp only [zero_smul, norm_zero, mul_zero, le_refl]

theorem dirichlet_normalized_square_probability (n : ℕ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hnorm : ‖f‖ ^ 2 = 1) :
    IsProbabilityMeasure (densityMeasure n (fun x => (f x) ^ 2)) := by
  have hmass : (∫ x, (f x) ^ 2) = 1 := by
    have h := l2_norm_sq_integral (volume : Measure (EuclideanSpace ℝ (Fin n))) f
    have hh : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using h
    exact hh.symm.trans hnorm
  refine ⟨?_⟩
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (Lp.memLp f).integrable_sq
      (ae_of_all volume fun x => sq_nonneg (f x)), hmass, ENNReal.ofReal_one]

theorem dirichletEigenvalue_pos_of_bounded (n : ℕ) (hn : 0 < n)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))).Nonempty)
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n)))) :
    0 < dirichletEigenvalue n U ∧ dirichletEigenvalue n U ≠ ∞ := by
  have hfinite := dirichletEigenvalue_ne_top n U hU
  refine ⟨pos_iff_ne_zero.mpr (fun hzero => ?_), hfinite⟩
  obtain ⟨ψ, hnorm, hRay, _hmin, _hweak⟩ := dirichletEigenvalue_attained_of_bounded n U hU hbounded
  have hgrad : dirichletGradient n U ψ = 0 := by
    have hE : ‖dirichletGradient n U ψ‖ ^ 2 = 0 := by
      simpa only [dirichletRayleigh, hnorm, div_one, hzero, ENNReal.toReal_zero] using hRay
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hE)
  letI := dirichlet_normalized_square_probability n (dirichletValue n U ψ) hnorm
  let i : Fin n := ⟨0, hn⟩
  have hc := sobolevFisher_square_root_coordinate n i
    (dirichletValue n U ψ) (dirichletGradient n U ψ)
    (Lp.memLp _) (Lp.memLp _) (dirichletValue_coordinate_memLp n U hbounded ψ)
    (sobolevFisher_graph_weak_square_product n ψ.val i)
  have hga : (dirichletGradient n U ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      =ᵐ[volume] fun _ => 0 := by
    rw [hgrad]
    exact Lp.coeFn_zero _ _ _
  have hz : (∫ x : EuclideanSpace ℝ (Fin n),
      (dirichletValue n U ψ x * x i) * dirichletGradient n U ψ x i) = 0 := by
    calc
      _ = ∫ _x : EuclideanSpace ℝ (Fin n), (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hga] with x hx
        rw [hx]
        simp
      _ = 0 := integral_zero _ _
  linarith [hc.2]

end AffineFKProof
