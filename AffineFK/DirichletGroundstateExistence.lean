module

public import AffineFK.DirichletRellichCompactness
public import AffineFK.DirichletGroundstateVariational
public import AffineFK.DirichletGroundstateSequence
public import AffineFK.DirichletGroundstateCompactLimit
public import AffineFK.DirichletGroundstateHilbert

/-!
# Attainment of the actual Dirichlet Rayleigh infimum

The genuine compact Dirichlet value map gives an L2-convergent subsequence
of normalized minimizing functions. Hilbert bounded-preimage compactness
and value-map injectivity then recover a unique H0^1 limit with optimal
gradient energy. The previously proved variational lemma supplies the
original weak eigen-equation. No minimizer, eigenfunction, or compactness
is assumed for the bounded-open conclusion.

This theorem does not assert positivity, simplicity, smoothness, evenness,
or log-concavity of the minimizer.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter
open scoped Topology

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem dirichletEigenvalue_attained_of_compact_value (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))).Nonempty)
    (hcompact : IsCompactOperator (dirichletValue n U)) :
    ∃ ψ : dirichletSobolev n U,
      ‖dirichletValue n U ψ‖ ^ 2 = 1 ∧
      dirichletRayleigh n U ψ = (dirichletEigenvalue n U).toReal ∧
      ENNReal.ofReal (dirichletRayleigh n U ψ) = dirichletEigenvalue n U ∧
      IsDirichletWeakEigenfunction n U (dirichletEigenvalue n U).toReal ψ := by
  let ell := (dirichletEigenvalue n U).toReal
  obtain ⟨v, hv, hE, hbound⟩ := dirichletGroundstate_bounded_minimizing_sequence n U hU
  letI := dirichletGroundstateInnerProductSpace n U
  obtain ⟨w, hwone, hwenergy⟩ := dirichletGroundstate_compact_minimizing_limit
    (V := dirichletSobolev n U)
    (F := Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (G := Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (dirichletValue n U) (dirichletGradient n U) (dirichletValue_injective n U)
    (dirichletGroundstate_graph_norm_sq n U) ell (Real.sqrt (ell + 2))
    ENNReal.toReal_nonneg v hv hE hbound hcompact
  have hne : dirichletValue n U w ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hwone
    exact zero_ne_one hwone
  have hlower : ell ≤ ‖dirichletGradient n U w‖ ^ 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (dirichletEigenvalue_le_rayleigh n U w hne)
    simpa only [dirichletRayleigh, hwone, div_one,
      ENNReal.toReal_ofReal (sq_nonneg ‖dirichletGradient n U w‖)] using h
  have hR : dirichletRayleigh n U w = ell := by
    unfold dirichletRayleigh
    rw [hwone, div_one]
    exact le_antisymm hwenergy hlower
  have hmin : ENNReal.ofReal (dirichletRayleigh n U w) = dirichletEigenvalue n U := by
    rw [hR]
    exact ENNReal.ofReal_toReal (dirichletEigenvalue_ne_top n U hU)
  refine ⟨w, hwone, hR, hmin, ?_⟩
  simpa only [hR] using dirichletRayleigh_attainment_weak_eigenfunction n U w hne hmin

theorem dirichletEigenvalue_attained_of_bounded (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))).Nonempty)
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n)))) :
    ∃ ψ : dirichletSobolev n U,
      ‖dirichletValue n U ψ‖ ^ 2 = 1 ∧
      dirichletRayleigh n U ψ = (dirichletEigenvalue n U).toReal ∧
      ENNReal.ofReal (dirichletRayleigh n U ψ) = dirichletEigenvalue n U ∧
      IsDirichletWeakEigenfunction n U (dirichletEigenvalue n U).toReal ψ :=
  dirichletEigenvalue_attained_of_compact_value n U hU (dirichletValue_isCompact_of_bounded n U hbounded)

end AffineFKProof
