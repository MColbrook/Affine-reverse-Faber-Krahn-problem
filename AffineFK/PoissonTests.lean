module

public import AffineFK.WeightedPoisson
public import AffineFK.SobolevApproximation

/-!
# Testing the Poisson equation on the whole H1 completion

The constant-one/zero-gradient element has been obtained by actual smooth
cutoffs. Subtracting the integral now gives a genuine mean-zero H1 element.
For a centred L2 source this extends the weak equation to every H1 test.
The completion is still represented by value-gradient pairs; identification
with a single-valued weak-gradient graph requires closability.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

/-- Subtracting the actual integral gives a mean-zero H1 element. -/
def centerSobolev
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (f : weightedSobolevGraph ν) : weightedSobolevMeanZero ν :=
  ⟨f - (l2Mean ν (sobolevValue ν f)) • sobolevOne n ν, by
    change l2Mean ν (sobolevValue ν (f - (l2Mean ν (sobolevValue ν f)) • sobolevOne n ν)) = 0
    simp only [map_sub, map_smul, sobolevOne_mean, smul_eq_mul, mul_one, sub_self]⟩

theorem centerSobolev_value
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (f : weightedSobolevGraph ν) :
    meanZeroValue ν (centerSobolev n ν f) = sobolevValue ν f -
      (l2Mean ν (sobolevValue ν f)) • Lp.const 2 ν (1 : ℝ) := by
  change sobolevValue ν (f - (l2Mean ν (sobolevValue ν f)) • sobolevOne n ν) = _
  simp only [map_sub, map_smul, sobolevOne_value]

theorem centerSobolev_gradient
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (f : weightedSobolevGraph ν) :
    meanZeroGradient ν (centerSobolev n ν f) = sobolevGradient ν f := by
  change sobolevGradient ν (f - (l2Mean ν (sobolevValue ν f)) • sobolevOne n ν) = _
  simp only [map_sub, map_smul, sobolevOne_gradient, smul_zero, sub_zero]

theorem l2_inner_one_eq_mean
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (g : Lp ℝ 2 ν) :
    ⟪g, Lp.const 2 ν (1 : ℝ)⟫ = l2Mean ν g := by
  exact real_inner_comm _ _

/-- For a centred source, the unique mean-zero solution satisfies the weak
equation for every test in the full constructed H1 completion. -/
theorem weighted_poisson_all_tests
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (hPnonneg : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (g : Lp ℝ 2 ν) (hg : l2Mean ν g = 0) :
    ∃! u : weightedSobolevGraph ν,
      l2Mean ν (sobolevValue ν u) = 0 ∧
      (∀ f : weightedSobolevGraph ν,
        ⟪sobolevGradient ν u, sobolevGradient ν f⟫ = ⟪g, sobolevValue ν f⟫) ∧
      ‖sobolevGradient ν u‖ ^ 2 ≤ P * ‖g‖ ^ 2 := by
  obtain ⟨u, hu, hunique⟩ := weighted_poisson_solution ν P hPnonneg hP g
  have hfull (f : weightedSobolevGraph ν) :
      ⟪sobolevGradient ν u.val, sobolevGradient ν f⟫ = ⟪g, sobolevValue ν f⟫ := by
    have h := hu.1 (centerSobolev n ν f)
    rw [centerSobolev_gradient, centerSobolev_value, inner_sub_right, inner_smul_right,
      l2_inner_one_eq_mean, hg, mul_zero, sub_zero] at h
    exact h
  refine ⟨u.val, ⟨meanZeroValue_mean ν u, hfull, hu.2⟩, ?_⟩
  intro w hw
  let w0 : weightedSobolevMeanZero ν := ⟨w, hw.1⟩
  have heq : w0 = u := hunique w0 ⟨fun v => hw.2.1 v.val, hw.2.2⟩
  exact congrArg Subtype.val heq

theorem l2_real_inner_integral
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (g f : Lp ℝ 2 ν) :
    ⟪g, f⟫ = ∫ x, g x * f x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  change f x * g x = g x * f x
  exact mul_comm _ _

/-- The same equation and energy estimate in the manuscript's actual
integral form, for every test in the constructed H1 completion. -/
theorem weighted_poisson_integral_all_tests
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (hPnonneg : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (g : Lp ℝ 2 ν) (hg : ∫ x, g x ∂ν = 0) :
    ∃! u : weightedSobolevGraph ν,
      (∫ x, (sobolevValue ν u) x ∂ν) = 0 ∧
      (∀ f : weightedSobolevGraph ν,
        (∫ x, ⟪(sobolevGradient ν u) x, (sobolevGradient ν f) x⟫ ∂ν) =
          ∫ x, g x * (sobolevValue ν f) x ∂ν) ∧
      (∫ x, ‖(sobolevGradient ν u) x‖ ^ 2 ∂ν) ≤ P * (∫ x, (g x) ^ 2 ∂ν) := by
  have hgmean : l2Mean ν g = 0 := (l2Mean_apply ν g).trans hg
  have hequiv (u : weightedSobolevGraph ν) :
      (l2Mean ν (sobolevValue ν u) = 0 ∧
        (∀ f : weightedSobolevGraph ν,
          ⟪sobolevGradient ν u, sobolevGradient ν f⟫ = ⟪g, sobolevValue ν f⟫) ∧
        ‖sobolevGradient ν u‖ ^ 2 ≤ P * ‖g‖ ^ 2) ↔
      ((∫ x, (sobolevValue ν u) x ∂ν) = 0 ∧
        (∀ f : weightedSobolevGraph ν,
          (∫ x, ⟪(sobolevGradient ν u) x, (sobolevGradient ν f) x⟫ ∂ν) =
            ∫ x, g x * (sobolevValue ν f) x ∂ν) ∧
        (∫ x, ‖(sobolevGradient ν u) x‖ ^ 2 ∂ν) ≤ P * (∫ x, (g x) ^ 2 ∂ν)) := by
    simp_rw [l2_real_inner_integral]
    simp only [l2Mean_apply, L2.inner_def,
      l2_norm_sq_integral, Real.norm_eq_abs, sq_abs]
  obtain ⟨u, hu, hunique⟩ := weighted_poisson_all_tests n ν P hPnonneg hP g hgmean
  exact ⟨u, (hequiv u).mp hu, fun w hw => hunique w ((hequiv w).mpr hw)⟩

end AffineFKProof
