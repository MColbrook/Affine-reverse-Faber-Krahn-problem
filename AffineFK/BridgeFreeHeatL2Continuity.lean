module

public import AffineFK.BridgeFreeHeatContinuity

/-!
# Actual strong L2 heat continuity, without regularity of the input

Compact-core self-pairings converge by two genuine dominated-convergence
arguments. The actual contraction converts this to strong L2 convergence,
which then extends through compact smooth density.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology Distributions RealInnerProductSpace

theorem bridgeFreeHeatL2_test_inner_tendsto (n : ℕ) (τ : ℕ → ℝ)
    (hpos : ∀ k, 0 < τ k) (hτ : Tendsto τ atTop (𝓝 0))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Tendsto (fun k => ⟪unweightedTestToL2 n φ,
      bridgeFreeHeatL2 n (τ k) (hpos k) (unweightedTestToL2 n φ)⟫)
        atTop (𝓝 (‖unweightedTestToL2 n φ‖^2)) := by
  obtain ⟨C, hC0, hC⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff 0
  have hb (y) : ‖φ y‖ ≤ C := by simpa only [norm_iteratedFDeriv_zero] using hC 0 le_rfl y
  have houter := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (bound := fun x => C * ‖φ x‖)
    (F := fun k x => φ x * bridgeFreeHeatAverage n (τ k) φ x) (f := fun x => (φ x)^2)
    (Eventually.of_forall fun k =>
      (φ.continuous.mul (bridgeFreeHeatAverage_test_smooth n (τ k) φ).continuous).aestronglyMeasurable)
    (Eventually.of_forall fun k => Eventually.of_forall fun x => by
      rw [norm_mul]
      calc
        _ ≤ ‖φ x‖ * C := mul_le_mul_of_nonneg_left
          (bridgeFreeHeatAverage_test_bound n φ C hb (τ k) x) (norm_nonneg _)
        _ = _ := mul_comm _ _)
    ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.const_mul C)
    (Eventually.of_forall fun x => by
      simpa only [pow_two] using tendsto_const_nhds.mul
        (bridgeFreeHeatAverage_test_tendsto n τ hτ φ x))
  have he (k : ℕ) : ⟪unweightedTestToL2 n φ,
      bridgeFreeHeatL2 n (τ k) (hpos k) (unweightedTestToL2 n φ)⟫ =
        ∫ x, φ x * bridgeFreeHeatAverage n (τ k) φ x ∂volume := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [unweightedTestToL2_coe n φ,
      bridgeFreeHeatL2_test_coe n (τ k) (hpos k) φ] with x hφ hQ
    simp [hφ, hQ, mul_comm]
  have hn : ‖unweightedTestToL2 n φ‖^2 = ∫ x, (φ x)^2 ∂volume := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [unweightedTestToL2_coe n φ] with x hx
    simp only [hx, Real.norm_eq_abs, sq_abs]
  simpa only [he, hn] using houter

set_option backward.isDefEq.respectTransparency false in
theorem bridgeFreeHeatL2_test_tendsto (n : ℕ) (τ : ℕ → ℝ)
    (hpos : ∀ k, 0 < τ k) (hτ : Tendsto τ atTop (𝓝 0))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Tendsto (fun k => bridgeFreeHeatL2 n (τ k) (hpos k) (unweightedTestToL2 n φ))
      atTop (𝓝 (unweightedTestToL2 n φ)) := by
  let a := unweightedTestToL2 n φ
  have hi := bridgeFreeHeatL2_test_inner_tendsto n τ hpos hτ φ
  change Tendsto (fun k => ⟪a, bridgeFreeHeatL2 n (τ k) (hpos k) a⟫)
    atTop (𝓝 (‖a‖^2)) at hi
  have hbound (k : ℕ) : ‖bridgeFreeHeatL2 n (τ k) (hpos k) a - a‖^2 ≤
      2 * (‖a‖^2 - ⟪a, bridgeFreeHeatL2 n (τ k) (hpos k) a⟫) := by
    have hn : ‖bridgeFreeHeatL2 n (τ k) (hpos k) a‖ ≤ ‖a‖ :=
      bridgeKilledL2Linear_norm_le n (τ k) (hpos k) univ isOpen_univ a
    have hn2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    rw [norm_sub_sq_real, real_inner_comm]
    nlinarith
  have hzero : Tendsto (fun k => 2 * (‖a‖^2 -
      ⟪a, bridgeFreeHeatL2 n (τ k) (hpos k) a⟫)) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := ‖a‖^2)).sub hi).const_mul 2
    have he : (‖a‖^2 - ‖a‖^2 : ℝ) = 0 := by ring
    rw [he, mul_zero] at h
    exact h
  have hsquare : Tendsto (fun k => ‖bridgeFreeHeatL2 n (τ k) (hpos k) a-a‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hbound hzero
  have hnorm : Tendsto (fun k => ‖bridgeFreeHeatL2 n (τ k) (hpos k) a-a‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsquare
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

theorem bridgeFreeHeatL2_tendsto_zero (n : ℕ) (τ : ℕ → ℝ)
    (hpos : ∀ k, 0 < τ k) (hτ : Tendsto τ atTop (𝓝 0))
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Tendsto (fun k => bridgeFreeHeatL2 n (τ k) (hpos k) f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have heps : 0 < ε/3 := by positivity
  obtain ⟨φ, hφ⟩ := bridge_unweighted_tests_dense n f
  obtain ⟨j, hj⟩ := Metric.tendsto_atTop.mp hφ (ε/3) heps
  let a := unweightedTestToL2 n (φ j)
  have haf : dist a f < ε/3 := hj j le_rfl
  have hcore := bridgeFreeHeatL2_test_tendsto n τ hpos hτ (φ j)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hcore (ε/3) heps
  refine ⟨N, fun k hk => ?_⟩
  have hc : dist (bridgeFreeHeatL2 n (τ k) (hpos k) f)
      (bridgeFreeHeatL2 n (τ k) (hpos k) a) ≤ dist f a := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact bridgeKilledL2Linear_norm_le n (τ k) (hpos k) univ isOpen_univ (f-a)
  have hdist := dist_triangle (bridgeFreeHeatL2 n (τ k) (hpos k) f)
    (bridgeFreeHeatL2 n (τ k) (hpos k) a) f
  have hdist' := dist_triangle (bridgeFreeHeatL2 n (τ k) (hpos k) a) a f
  have hmiddle : dist (bridgeFreeHeatL2 n (τ k) (hpos k) a) a < ε/3 := hN k hk
  have haf' : dist f a < ε/3 := by simpa only [dist_comm] using haf
  linarith

end AffineFKProof
