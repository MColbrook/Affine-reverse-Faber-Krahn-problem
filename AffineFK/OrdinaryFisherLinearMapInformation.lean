module

public import AffineFK.FisherInformation
public import AffineFK.OrdinaryFisherLinearMapEnergy

/-!
# The actual extended ordinary Fisher inequality under invertible linear maps

The finite case uses direct transport of actual compact-test H1
approximations and the exact inverse-determinant density. For positive
dimension the inverse operator norm is strictly positive, so infinite
input information gives an infinite right side. Dimension zero is
handled by its genuine zero Sobolev gradient energy, including the
otherwise delicate zero-times-infinity convention.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped ENNReal Distributions RealInnerProductSpace

theorem fisherInformation_zero_dimension
    (ρ : EuclideanSpace ℝ (Fin 0) → ℝ) : fisherInformation 0 ρ = 0 := by
  let E := EuclideanSpace ℝ (Fin 0)
  have hsub : ∀ x y : E, x = y := fun x y => by ext i; exact Fin.elim0 i
  let : Subsingleton E := ⟨hsub⟩
  have heq : (Set.univ : Set E) = {0} := by
    ext x
    simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
    exact hsub x 0
  let : CompactSpace E := ⟨by rw [heq]; exact isCompact_singleton⟩
  let φ : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨fun _ => Real.sqrt (ρ 0), contDiff_const,
      HasCompactSupport.of_compactSpace _, Set.subset_univ _⟩
  let v : unweightedSobolevGraph 0 := ⟨unweightedSmoothPair 0 φ, unweighted_smooth_pair_mem 0 φ⟩
  have hv : (unweightedValue 0 v : E → ℝ) =ᵐ[volume] fun x => Real.sqrt (ρ x) := by
    have hval : unweightedValue 0 v = unweightedTestToL2 0 φ := rfl
    rw [hval]
    apply (unweightedTestToL2_coe 0 φ).trans
    exact Filter.Eventually.of_forall fun x => by
      change Real.sqrt (ρ 0) = Real.sqrt (ρ x)
      rw [hsub x 0]
  rw [fisherInformation_eq_graph 0 ρ v hv]
  have hg : (fun x : E => ‖unweightedGradient 0 v x‖ ^ 2) = fun _ => (0 : ℝ) := by
    funext x
    rw [hsub (unweightedGradient 0 v x) 0]
    norm_num
  rw [hg, integral_zero]
  norm_num

theorem fisherInformation_linearMap (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) :
    fisherInformation n (ordinaryFisherLinearDensity n A ρ) ≤
      ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2) * fisherInformation n ρ := by
  by_cases hn : n = 0
  · subst n
    rw [fisherInformation_zero_dimension, fisherInformation_zero_dimension, mul_zero]
  · let : NeZero n := ⟨hn⟩
    by_cases htop : fisherInformation n ρ = ∞
    · have hc : ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos A.symm.norm_pos))
      rw [htop, ENNReal.mul_top hc]
      exact le_top
    · obtain ⟨v, hv⟩ := (fisherInformation_ne_top_iff n ρ).mp htop
      obtain ⟨w, hw, _hgradient, henergy⟩ := ordinaryFisher_linear_sqrt_H1_energy n A ρ v hv
      rw [fisherInformation_eq_graph n _ w hw, fisherInformation_eq_graph n ρ v hv,
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal henergy

theorem fisherInformation_linearMap_with_law (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ) :
    (densityMeasure n ρ).map A = densityMeasure n (ordinaryFisherLinearDensity n A ρ) ∧
    fisherInformation n (ordinaryFisherLinearDensity n A ρ) ≤
      ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2) * fisherInformation n ρ := by
  exact ⟨ordinaryFisherLinearDensity_law n A ρ hρ,
    fisherInformation_linearMap n A ρ⟩

end AffineFKProof
