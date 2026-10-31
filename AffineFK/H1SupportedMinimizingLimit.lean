module

public import AffineFK.H1LocalizedCompactness
public import AffineFK.DirichletGroundstateVariational
public import AffineFK.DirichletRayleighFinite

/-!
# Genuine H0 minimizing limits of supported Gaussian competitors

Compact localization is used only to extract a strong L2 limit. The
energy estimate is passed through the original global H1 approximants,
so neither a cutoff factor nor a dimension factor changes the energy.
The final variational argument reuses the actual attainment mechanism
in `DirichletGroundstateExistence`, independently of its minimizing sequence.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem supported_h1_normalized_limit_energy (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (f : ℕ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (v : ℕ → unweightedSobolevGraph n) (R : ℝ) (hbound : ∀ k, ‖v k‖ ≤ R)
    (hnorm : ∀ k, ‖f k‖^2 = 1)
    (hsupp : ∀ k, ∀ᵐ x ∂volume,
      x ∉ closure (U : Set (EuclideanSpace ℝ (Fin n))) → f k x = 0)
    (hclose : Tendsto (fun k => unweightedValue n (v k) - f k) atTop (𝓝 0))
    (b : ℕ → ℝ) (B : ℝ)
    (hgrad : ∀ k, ‖unweightedGradient n (v k)‖^2 ≤ b k)
    (hb : Tendsto b atTop (𝓝 B)) :
    ∃ ψ : dirichletSobolev n U, ∃ s : ℕ → ℕ,
      StrictMono s ∧ ‖dirichletValue n U ψ‖^2 = 1 ∧
      ‖dirichletGradient n U ψ‖^2 ≤ B ∧
      Tendsto (fun k => f (s k)) atTop (𝓝 (dirichletValue n U ψ)) := by
  obtain ⟨g, s, hs, hfg⟩ := supported_l2_near_h1_subsequence n
    (closure (U : Set (EuclideanSpace ℝ (Fin n)))) hbounded.isCompact_closure f v R hbound hsupp hclose
  have hval : Tendsto (fun k => unweightedValue n (v (s k))) atTop (𝓝 g) := by
    have h := (hclose.comp hs.tendsto_atTop).add hfg
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using h
  obtain ⟨w, hw, hE⟩ := bridge_unweighted_graph_limit_energy n (fun k => v (s k))
    g (fun k => b (s k)) B (fun k => hgrad (s k)) (hb.comp hs.tendsto_atTop) hval
  have hwsupp : ∀ᵐ x ∂volume,
      x ∉ closure (U : Set (EuclideanSpace ℝ (Fin n))) → unweightedValue n w x = 0 := by
    rw [hw]
    exact supported_l2_limit n _ (fun k => f (s k)) g (fun k => hsupp (s k)) hfg
  have hwmem := unweighted_mem_dirichlet_of_zero_exterior n U hconv hzero hbounded w hwsupp
  let ψ : dirichletSobolev n U := ⟨w, hwmem⟩
  have hψ : dirichletValue n U ψ = g := hw
  have hgone : ‖g‖^2 = 1 := by
    have hone : Tendsto (fun k => ‖f (s k)‖^2) atTop (𝓝 (1 : ℝ)) := by
      simpa only [hnorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique (hfg.norm.pow 2) hone
  refine ⟨ψ, s, hs, ?_, hE, ?_⟩
  · rw [hψ, hgone]
  · rwa [hψ]

theorem supported_h1_normalized_minimizing_limit (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (f : ℕ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (v : ℕ → unweightedSobolevGraph n) (R : ℝ) (hbound : ∀ k, ‖v k‖ ≤ R)
    (hnorm : ∀ k, ‖f k‖^2 = 1)
    (hsupp : ∀ k, ∀ᵐ x ∂volume,
      x ∉ closure (U : Set (EuclideanSpace ℝ (Fin n))) → f k x = 0)
    (hclose : Tendsto (fun k => unweightedValue n (v k) - f k) atTop (𝓝 0))
    (b : ℕ → ℝ) (hgrad : ∀ k, ‖unweightedGradient n (v k)‖^2 ≤ b k)
    (hb : Tendsto b atTop (𝓝 (dirichletEigenvalue n U).toReal)) :
    ∃ ψ : dirichletSobolev n U, ∃ s : ℕ → ℕ,
      StrictMono s ∧ ‖dirichletValue n U ψ‖^2 = 1 ∧
      dirichletRayleigh n U ψ = (dirichletEigenvalue n U).toReal ∧
      ENNReal.ofReal (dirichletRayleigh n U ψ) = dirichletEigenvalue n U ∧
      IsDirichletWeakEigenfunction n U (dirichletEigenvalue n U).toReal ψ ∧
      Tendsto (fun k => f (s k)) atTop (𝓝 (dirichletValue n U ψ)) := by
  obtain ⟨ψ, s, hs, hone, hE, hlim⟩ := supported_h1_normalized_limit_energy n U
    hconv hzero hbounded f v R hbound hnorm hsupp hclose b (dirichletEigenvalue n U).toReal hgrad hb
  have hne : dirichletValue n U ψ ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hone
    exact zero_ne_one hone
  have hlower : (dirichletEigenvalue n U).toReal ≤ ‖dirichletGradient n U ψ‖^2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (dirichletEigenvalue_le_rayleigh n U ψ hne)
    simpa only [dirichletRayleigh, hone, div_one,
      ENNReal.toReal_ofReal (sq_nonneg ‖dirichletGradient n U ψ‖)] using h
  have hR : dirichletRayleigh n U ψ = (dirichletEigenvalue n U).toReal := by
    rw [dirichletRayleigh, hone, div_one]
    exact le_antisymm hE hlower
  have hmin : ENNReal.ofReal (dirichletRayleigh n U ψ) = dirichletEigenvalue n U := by
    rw [hR]
    exact ENNReal.ofReal_toReal (dirichletEigenvalue_ne_top n U ⟨0, hzero⟩)
  refine ⟨ψ, s, hs, hone, hR, hmin, ?_, hlim⟩
  simpa only [hR] using dirichletRayleigh_attainment_weak_eigenfunction n U ψ hne hmin

end AffineFKProof
