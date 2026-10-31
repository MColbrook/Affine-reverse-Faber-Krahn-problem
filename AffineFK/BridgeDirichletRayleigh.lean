module

public import AffineFK.BridgeKilledRowSobolev
public import AffineFK.DirichletSupportConverse

/-!
# The actual variational Dirichlet bound from killed bridge diagonals

The proved killed-row H1 construction and actual zero-exterior H0 theorem
supply a genuine nonzero Rayleigh competitor. No spectral expansion,
Dirichlet heat-kernel identification, or eigenvalue proxy is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
theorem bridgeKilledRow_dirichlet_energy (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (a : ℝ) (ha : 0 < a)
    (hpos : ∀ r : ℝ, a ≤ r → r ≤ 3*a → 0 < bridgeKilledDiagonal n r 0 U) :
    ∃ v : dirichletSobolev n U,
      dirichletValue n U v = bridgeKilledRowL2 n a ha 0 U U.isOpen ∧
      ‖dirichletGradient n U v‖^2 ≤ (2/a) * bridgeKilledDiagonal n (2*a) 0 U *
        (Real.log (bridgeKilledDiagonal n a 0 U) - Real.log (bridgeKilledDiagonal n (2*a) 0 U)) := by
  obtain ⟨v, hv, hG⟩ := bridgeKilledRowL2_has_sobolev_energy n a ha 0 U U.isOpen hpos
  have hsupp : ∀ᵐ y ∂volume, y ∉ closure (U : Set (EuclideanSpace ℝ (Fin n))) →
      unweightedValue n v y = 0 := by
    rw [hv]
    filter_upwards [bridgeKilledRowL2_zero_exterior n a ha 0 U U.isOpen] with y hy
    intro hyc
    exact hy (fun hyU => hyc (subset_closure hyU))
  have hmem := unweighted_mem_dirichlet_of_zero_exterior n U hconv hzero hbounded v hsupp
  exact ⟨⟨v, hmem⟩, hv, hG⟩

set_option backward.isDefEq.respectTransparency false in
theorem bridge_dirichletEigenvalue_le_log_diagonal (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (a : ℝ) (ha : 0 < a)
    (hpos : ∀ r : ℝ, a ≤ r → r ≤ 3*a → 0 < bridgeKilledDiagonal n r 0 U) :
    dirichletEigenvalue n U ≤ ENNReal.ofReal ((2/a) *
      (Real.log (bridgeKilledDiagonal n a 0 U) - Real.log (bridgeKilledDiagonal n (2*a) 0 U))) := by
  obtain ⟨v, hv, hG⟩ := bridgeKilledRow_dirichlet_energy n U hconv hzero hbounded a ha hpos
  have hd : 0 < bridgeKilledDiagonal n (2*a) 0 U := hpos _ (by linarith) (by linarith)
  have hn : ‖dirichletValue n U v‖^2 = bridgeKilledDiagonal n (2*a) 0 U := by
    rw [hv, bridgeKilledRowL2_norm_sq]
    rfl
  have hv0 : dirichletValue n U v ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
    linarith
  apply (dirichletEigenvalue_le_rayleigh n U v hv0).trans
  apply ENNReal.ofReal_le_ofReal
  unfold dirichletRayleigh
  rw [hn]
  apply (div_le_iff₀ hd).mpr
  nlinarith

end AffineFKProof
