module

public import AffineFK.H1SupportedMinimizingLimit
public import AffineFK.H1GaussianDirichletEnergy
public import AffineFK.GaussianL2HeatIdentification

/-!
# Actual nonlocal Gaussian competitors give genuine Dirichlet minimizers

The free Gaussian average has a completed H1 gradient with energy at most
its actual nonlocal form. A vanishing positive time step then supplies
the exact nearby H1 elements needed by the supported compactness theorem.
No H1 approximant or spectral convergence assertion is an input here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter InnerProductSpace Set
open scoped Topology RealInnerProductSpace ENNReal

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem gaussianL2Average_graph_energy_le_form (n : ℕ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ v : unweightedSobolevGraph n,
      unweightedValue n v = bridgeGaussianL2Average n (Real.sqrt h) f ∧
      ‖unweightedGradient n v‖^2 ≤ h1GaussianDirichletForm n h f := by
  obtain ⟨v, hv, hg⟩ := bridgeFreeHeatL2_has_graph_energy n h hh f
  rw [← gaussianL2Average_eq_heat n h hh f] at hv hg
  have hsq := sq_nonneg ‖f - bridgeGaussianL2Average n (Real.sqrt h) f‖
  rw [norm_sub_sq_real] at hsq
  have hraw : ‖f‖^2 - ‖bridgeGaussianL2Average n (Real.sqrt h) f‖^2 ≤
      2 * (‖f‖^2 - ⟪f, bridgeGaussianL2Average n (Real.sqrt h) f⟫) := by
    nlinarith
  have hF : h * h1GaussianDirichletForm n h f =
      2 * (‖f‖^2 - ⟪f, bridgeGaussianL2Average n (Real.sqrt h) f⟫) := by
    unfold h1GaussianDirichletForm
    field_simp
  refine ⟨v, hv, ?_⟩
  have hbound := hg.trans hraw
  rw [← hF] at hbound
  nlinarith

theorem gaussianL2Average_form_sequence_close (n : ℕ)
    (f : ℕ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (h b : ℕ → ℝ) (B : ℝ) (hh : ∀ k, 0 < h k)
    (ht : Tendsto h atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 B))
    (hform : ∀ k, h1GaussianDirichletForm n (h k) (f k) ≤ b k) :
    Tendsto (fun k => bridgeGaussianL2Average n (Real.sqrt (h k)) (f k) - f k)
      atTop (𝓝 0) := by
  have hupper (k : ℕ) :
      ‖bridgeGaussianL2Average n (Real.sqrt (h k)) (f k) - f k‖^2 ≤ h k * b k :=
    (gaussianL2Average_sub_norm_sq_le_form n (h k) (hh k) (f k)).trans
      (mul_le_mul_of_nonneg_left (hform k) (hh k).le)
  have hsquare : Tendsto
      (fun k => ‖bridgeGaussianL2Average n (Real.sqrt (h k)) (f k) - f k‖^2)
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun k => sq_nonneg _) hupper (by simpa only [zero_mul] using ht.mul hb)
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  have hn : Tendsto
      (fun k => ‖bridgeGaussianL2Average n (Real.sqrt (h k)) (f k) - f k‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hnorm
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

theorem gaussian_supported_normalized_minimizing_limit (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (f : ℕ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hnorm : ∀ k, ‖f k‖^2 = 1)
    (hsupp : ∀ k, ∀ᵐ x ∂volume,
      x ∉ closure (U : Set (EuclideanSpace ℝ (Fin n))) → f k x = 0)
    (h b : ℕ → ℝ) (hh : ∀ k, 0 < h k) (ht : Tendsto h atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 (dirichletEigenvalue n U).toReal))
    (hform : ∀ k, h1GaussianDirichletForm n (h k) (f k) ≤ b k) :
    ∃ ψ : dirichletSobolev n U, ∃ s : ℕ → ℕ,
      StrictMono s ∧ ‖dirichletValue n U ψ‖^2 = 1 ∧
      dirichletRayleigh n U ψ = (dirichletEigenvalue n U).toReal ∧
      ENNReal.ofReal (dirichletRayleigh n U ψ) = dirichletEigenvalue n U ∧
      IsDirichletWeakEigenfunction n U (dirichletEigenvalue n U).toReal ψ ∧
      Tendsto (fun k => f (s k)) atTop (𝓝 (dirichletValue n U ψ)) := by
  choose v hv hg using fun k => gaussianL2Average_graph_energy_le_form n (h k) (hh k) (f k)
  have hgrad (k : ℕ) : ‖unweightedGradient n (v k)‖^2 ≤ b k := (hg k).trans (hform k)
  obtain ⟨C, hC⟩ := hb.bddAbove_range
  have hbound (k : ℕ) : ‖v k‖ ≤ Real.sqrt (max (1 + C) 0) := by
    have hQ := pow_le_pow_left₀
      (norm_nonneg (bridgeGaussianL2Average n (Real.sqrt (h k)) (f k)))
      (bridgeGaussianL2Average_norm_le n (Real.sqrt (h k)) (f k)) 2
    rw [hnorm k] at hQ
    have hE := (hgrad k).trans (hC ⟨k, rfl⟩)
    have hsq : ‖v k‖^2 ≤ max (1 + C) 0 := by
      rw [unweighted_graph_norm_sq, hv k]
      have hm := le_max_left (1 + C) 0
      linarith
    exact (Real.le_sqrt (norm_nonneg _) (le_max_right _ _)).mpr hsq
  have hclose : Tendsto (fun k => unweightedValue n (v k) - f k) atTop (𝓝 0) := by
    simpa only [hv] using gaussianL2Average_form_sequence_close n f h b
      (dirichletEigenvalue n U).toReal hh ht hb hform
  exact supported_h1_normalized_minimizing_limit n U hconv hzero hbounded f v
    (Real.sqrt (max (1 + C) 0)) hbound hnorm hsupp hclose b hgrad hb

end AffineFKProof
