module

public import AffineFK.FiniteSobolevWeakScore

/-!
# The actual square-root-density Sobolev domain

The graph value is required to equal the density's actual nonnegative
square root almost everywhere for Lebesgue volume. The injective value map
makes its graph gradient unique. The resulting field lives on the actual
original density measure, has finite L2 energy bounded by the manuscript's
Sobolev expression, and satisfies its weak score equation for every compact
smooth vector field. The equation is derived, not assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem finiteSobolev_square_root_graph_unique (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (v w : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x))
    (hw : (unweightedValue n w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) : v = w := by
  apply unweighted_sobolev_value_injective n
  exact Lp.ext (hv.trans hw.symm)

theorem finiteSobolev_square_density_eq (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) :
    densityMeasure n ρ = densityMeasure n (fun x => (unweightedValue n v x) ^ 2) := by
  unfold densityMeasure
  apply withDensity_congr_ae
  filter_upwards [hv, hρ0] with x hx h0
  rw [hx, Real.sq_sqrt h0]

theorem finiteSobolev_density_relative_score (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x))
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ)) :
    ∃ s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable s ∧ MemLp s 2 (densityMeasure n ρ) ∧
      (s =ᵐ[densityMeasure n ρ]
        fun x => (2 / Real.sqrt (ρ x)) • unweightedGradient n v x + x) ∧
      Integrable (fun x => ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, ‖s x‖ ^ 2 ∂densityMeasure n ρ) ≤
        (∫ x, ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2) ∧
      ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
        Integrable (fun x => ⟪s x, F x⟫) (densityMeasure n ρ) ∧
        Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) (densityMeasure n ρ) ∧
        (∫ x, ⟪s x, F x⟫ ∂densityMeasure n ρ) =
          ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ := by
  have heq := finiteSobolev_square_density_eq n ρ hρ0 v hv
  let : IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) := by
    rw [← heq]
    infer_instance
  have hsecond' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) := by
    rw [← heq]
    exact hsecond
  have hs := finiteSobolev_graph_relative_score n v hsecond'
  have hxf := finiteSobolev_x_value_memLp_of_second_moment n v hsecond'
  have hA := ((Lp.memLp (unweightedGradient n v)).const_smul (2 : ℝ)).add hxf
  have hA2 := (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA
  have hAE : (fun x => ‖(2 : ℝ) • unweightedGradient n v x + unweightedValue n v x • x‖ ^ 2) =ᵐ[volume]
      fun x => ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2 := by
    filter_upwards [hv] with x hx
    rw [hx]
  refine ⟨finiteSobolevGraphScore n v, hs.1, ?_, ?_, hA2.congr hAE, ?_, ?_⟩
  · simpa only [heq] using hs.2.1
  · have hac : densityMeasure n ρ ≪ volume := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le hv] with x hx
    change (2 / unweightedValue n v x) • unweightedGradient n v x + x = _
    rw [hx]
  · have hbound := hs.2.2.1
    rw [integral_congr_ae hAE] at hbound
    simpa only [heq] using hbound
  · intro F
    simpa only [heq] using hs.2.2.2 F

end AffineFKProof
