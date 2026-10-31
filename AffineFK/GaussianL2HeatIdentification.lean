module

public import AffineFK.BridgeGaussianL2Average
public import AffineFK.BridgeFreeHeatSobolev
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Hilbert-valued Gaussian average is the actual free heat operator

Compact smooth pairings justify Fubini before either order of integration
is used. Genuine L2 density and the two contraction estimates then give
the identity for every L2 input. In particular, the Bochner average and
the independently constructed Brownian heat kernel are not conflated.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology Distributions RealInnerProductSpace

theorem gaussianL2Average_sub (n : ℕ) (b : ℝ)
    (f g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    bridgeGaussianL2Average n b (f-g) =
      bridgeGaussianL2Average n b f - bridgeGaussianL2Average n b g := by
  simp only [bridgeGaussianL2Average, map_sub]
  exact integral_sub (bridgeGaussianL2Average_integrable n b f)
    (bridgeGaussianL2Average_integrable n b g)

theorem gaussianL2Average_lipschitz (n : ℕ) (b : ℝ) :
    LipschitzWith 1 (bridgeGaussianL2Average n b) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [← gaussianL2Average_sub]
  exact bridgeGaussianL2Average_norm_le n b (f-g)

theorem gaussianL2Average_test_pairing (n : ℕ) (h : ℝ) (hh : 0 < h)
    (φ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ⟪unweightedTestToL2 n ψ,
      bridgeGaussianL2Average n (Real.sqrt h) (unweightedTestToL2 n φ)⟫ =
      ⟪unweightedTestToL2 n ψ,
        bridgeFreeHeatL2 n h hh (unweightedTestToL2 n φ)⟫ := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  obtain ⟨C, _, hC⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff 0
  have hb (y : E) : ‖φ y‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using hC 0 le_rfl y
  have hψ : Integrable ψ (volume : Measure E) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  let F : E × E → ℝ := fun p => ψ p.2 * φ (p.2 + Real.sqrt h • p.1)
  have hF : Integrable F (γ.prod volume) := by
    apply ((integrable_const C).mul_prod hψ.norm).mono'
      ((ψ.continuous.comp continuous_snd).mul
        (φ.continuous.comp (by fun_prop))).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      dsimp [F]
      change ‖ψ p.2 * φ (p.2 + Real.sqrt h • p.1)‖ ≤ C * ‖ψ p.2‖
      rw [norm_mul]
      calc
        _ ≤ ‖ψ p.2‖ * C := mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
        _ = _ := mul_comm _ _
  have htrans (u : E) :
      ⟪unweightedTestToL2 n ψ,
        bridgeL2Translate n (Real.sqrt h • u) (unweightedTestToL2 n φ)⟫ =
        ∫ x, F (u,x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have hshift := (measurePreserving_add_right (volume : Measure E) (Real.sqrt h • u)).quasiMeasurePreserving.ae_eq_comp
      (unweightedTestToL2_coe n φ)
    filter_upwards [unweightedTestToL2_coe n ψ,
      bridgeL2Translate_coe n (Real.sqrt h • u) (unweightedTestToL2 n φ), hshift]
      with x hψx htx hφx
    change unweightedTestToL2 n φ (x + Real.sqrt h • u) = φ (x + Real.sqrt h • u) at hφx
    simp only [hψx, htx, hφx, F, RCLike.inner_apply, conj_trivial, mul_comm]
  calc
    _ = ∫ u, ⟪unweightedTestToL2 n ψ,
        bridgeL2Translate n (Real.sqrt h • u) (unweightedTestToL2 n φ)⟫ ∂γ :=
      (integral_inner (bridgeGaussianL2Average_integrable n (Real.sqrt h)
        (unweightedTestToL2 n φ)) _).symm
    _ = ∫ u, ∫ x, F (u,x) ∂volume ∂γ := integral_congr_ae (Eventually.of_forall htrans)
    _ = ∫ x, ∫ u, F (u,x) ∂γ := integral_integral_swap hF
    _ = ∫ x, ψ x * bridgeFreeHeatAverage n h φ x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => integral_const_mul (ψ x) _
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [unweightedTestToL2_coe n ψ, bridgeFreeHeatL2_test_coe n h hh φ]
        with x hψx hφx
      simp only [hψx, hφx, RCLike.inner_apply, conj_trivial, mul_comm]

theorem gaussianL2Average_test_eq_heat (n : ℕ) (h : ℝ) (hh : 0 < h)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    bridgeGaussianL2Average n (Real.sqrt h) (unweightedTestToL2 n φ) =
      bridgeFreeHeatL2 n h hh (unweightedTestToL2 n φ) := by
  apply ext_inner_left ℝ
  intro f
  obtain ⟨ψ, hψ⟩ := bridge_unweighted_tests_dense n f
  have hl := hψ.inner (𝕜 := ℝ) (tendsto_const_nhds (x :=
    bridgeGaussianL2Average n (Real.sqrt h) (unweightedTestToL2 n φ)))
  have hr := hψ.inner (𝕜 := ℝ) (tendsto_const_nhds (x :=
    bridgeFreeHeatL2 n h hh (unweightedTestToL2 n φ)))
  have he : (fun k => ⟪unweightedTestToL2 n (ψ k),
      bridgeGaussianL2Average n (Real.sqrt h) (unweightedTestToL2 n φ)⟫) =
      (fun k => ⟪unweightedTestToL2 n (ψ k),
        bridgeFreeHeatL2 n h hh (unweightedTestToL2 n φ)⟫) :=
    funext (fun k => gaussianL2Average_test_pairing n h hh φ (ψ k))
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

theorem gaussianL2Average_eq_heat (n : ℕ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    bridgeGaussianL2Average n (Real.sqrt h) f = bridgeFreeHeatL2 n h hh f := by
  obtain ⟨φ, hφ⟩ := bridge_unweighted_tests_dense n f
  have hl := ((gaussianL2Average_lipschitz n (Real.sqrt h)).continuous.tendsto f).comp hφ
  have hr := ((bridgeFreeHeatL2 n h hh).continuous.tendsto f).comp hφ
  have he : (bridgeGaussianL2Average n (Real.sqrt h) ∘ fun k => unweightedTestToL2 n (φ k)) =
      ((bridgeFreeHeatL2 n h hh) ∘ fun k => unweightedTestToL2 n (φ k)) :=
    funext (fun k => gaussianL2Average_test_eq_heat n h hh (φ k))
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

end AffineFKProof
