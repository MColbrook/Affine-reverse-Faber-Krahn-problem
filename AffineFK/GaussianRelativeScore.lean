module

public import AffineFK.LogDensityIntegration
public import AffineFK.VectorTestUniqueness

/-!
# The relative Gaussian score in terms of a Lebesgue density

For a smooth positive density rho the density formula for the relative
Gaussian score is grad(log rho)+x. Its compact-test identity determines
it among L2 vector fields, and supplies its L2 membership without that
membership being assumed. Transport of an actual smoothed law to a
smooth density remains a separate assertion.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff

def gaussianRelativeScore
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  gradient (fun y => Real.log (ρ y)) x + x

theorem gaussianRelativeScore_continuous
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) : Continuous (gaussianRelativeScore n ρ) :=
  (continuous_log_density_gradient n ρ hρ hρpos).add continuous_id

theorem gaussianRelativeScore_component_pairing
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => gaussianRelativeScore n ρ x j * φ x) (densityMeasure n ρ) ∧
    Integrable (fun x => x j * φ x) (densityMeasure n ρ) ∧
    Integrable (partialTest n j φ) (densityMeasure n ρ) ∧
    (∫ x, gaussianRelativeScore n ρ x j * φ x ∂densityMeasure n ρ) =
      (∫ x, x j * φ x ∂densityMeasure n ρ) - ∫ x, partialTest n j φ x ∂densityMeasure n ρ := by
  have hl := log_density_gradient_test_integration_by_parts n ρ hρ hρpos j φ
  have hx : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x j * φ x) (densityMeasure n ρ) :=
    ((by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x j)).mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  have heq : (fun x => gaussianRelativeScore n ρ x j * φ x) =
      (fun x => gradient (fun y => Real.log (ρ y)) x j * φ x + x j * φ x) := by
    funext x
    simp only [gaussianRelativeScore, PiLp.add_apply, add_mul]
  refine ⟨?_, hx, hl.2.1, ?_⟩
  · rw [heq]
    exact hl.1.add hx
  · rw [heq, integral_add hl.1 hx, hl.2.2]
    ring

theorem gaussianRelativeScore_vector_pairing
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n))) :
    Integrable (fun x => ⟪gaussianRelativeScore n ρ x, F x⟫) (densityMeasure n ρ) ∧
    Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) (densityMeasure n ρ) ∧
    (∫ x, ⟪gaussianRelativeScore n ρ x, F x⟫ ∂densityMeasure n ρ) =
      ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ := by
  let ν := densityMeasure n ρ
  have hc (i : Fin n) := gaussianRelativeScore_component_pairing n ρ hρ hρpos i (vectorComponentTest n i F)
  have hr (i : Fin n) : Integrable (fun x =>
      x i * vectorComponentTest n i F x - partialTest n i (vectorComponentTest n i F) x) ν :=
    (hc i).2.1.sub (hc i).2.2.1
  have hleft : (fun x => ⟪gaussianRelativeScore n ρ x, F x⟫) =
      (fun x => ∑ i : Fin n, gaussianRelativeScore n ρ x i * vectorComponentTest n i F x) := by
    funext x
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, vectorComponentTest_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hright : (fun x => ⟪x, F x⟫ - vectorDivergence n F x) =
      (fun x => ∑ i : Fin n,
        (x i * vectorComponentTest n i F x - partialTest n i (vectorComponentTest n i F) x)) :=
    funext (vector_stein_left_sum n F)
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact integrable_finsetSum _ fun i _ => (hc i).1
  · rw [hright]
    exact integrable_finsetSum _ fun i _ => hr i
  · rw [hleft, hright, integral_finsetSum _ fun i _ => (hc i).1,
      integral_finsetSum _ fun i _ => hr i]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_sub (hc i).2.1 (hc i).2.2.1]
    exact (hc i).2.2.2

theorem gaussianRelativeScore_identified_by_weak_identity
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : MemLp r 2 (densityMeasure n ρ))
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪r x, F x⟫ ∂densityMeasure n ρ) =
        ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ) :
    r =ᵐ[densityMeasure n ρ] gaussianRelativeScore n ρ ∧
    MemLp (gaussianRelativeScore n ρ) 2 (densityMeasure n ρ) ∧
    (∫ x, ‖gaussianRelativeScore n ρ x‖ ^ 2 ∂densityMeasure n ρ) =
      ∫ x, ‖r x‖ ^ 2 ∂densityMeasure n ρ := by
  apply continuous_vector_field_L2_of_test_pairings n (densityMeasure n ρ) r (gaussianRelativeScore n ρ)
    hr (gaussianRelativeScore_continuous n ρ hρ hρpos)
  intro F
  exact (hweak F).trans (gaussianRelativeScore_vector_pairing n ρ hρ hρpos F).2.2.symm

end AffineFKProof
