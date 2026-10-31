module

public import AffineFK.BridgeFreeHeatEnergy
public import AffineFK.BridgeKilledL2Operator
public import AffineFK.BridgeSobolevEnergyLimit
public import AffineFK.UnweightedSobolevSmoothApproximation
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Free Gaussian heat averaging maps actual L2 into the actual H1 graph

Mathlib's genuine smooth compact Lp approximation is due to Sebastien
Gouezel and contributors. The compact-core energy estimate passes to the
completed graph using proved weak Hilbert compactness and scalar energy
bounds; no weak derivative or smoothing conclusion is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set TopologicalSpace Filter
open scoped ENNReal Distributions RealInnerProductSpace Topology

theorem bridge_unweighted_tests_dense (n : ℕ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ φ : ℕ → 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      Tendsto (fun k => unweightedTestToL2 n (φ k)) atTop (𝓝 f) := by
  have hd := MeasureTheory.Lp.dense_hasCompactSupport_contDiff
    (E := EuclideanSpace ℝ (Fin n)) (F := ℝ) (μ := volume) (p := 2) (by norm_num)
  obtain ⟨u, hu, hlimit⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose g hae hcompact hsmooth using hu
  let φ : ℕ → 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
    fun k => ⟨g k, hsmooth k, hcompact k, subset_univ _⟩
  have he (k : ℕ) : unweightedTestToL2 n (φ k) = u k := by
    apply Lp.ext
    exact (unweightedTestToL2_coe n (φ k)).trans (hae k).symm
  exact ⟨φ, by simpa only [he] using hlimit⟩

def bridgeFreeHeatL2 (n : ℕ) (t : ℝ) (ht : 0 < t) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  bridgeKilledL2Operator n t ht univ isOpen_univ

theorem bridgeFreeHeatL2_test_coe (n : ℕ) (t : ℝ) (ht : 0 < t)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (bridgeFreeHeatL2 n t ht (unweightedTestToL2 n φ) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] bridgeFreeHeatAverage n t φ := by
  have hi := bridgeKilledIntegral_congr_ae_input n t ht univ isOpen_univ _ _
    (unweightedTestToL2_coe n φ)
  have he := bridgeKilledL2Operator_coe n t ht univ isOpen_univ (unweightedTestToL2 n φ)
  rw [hi, ← bridgeFreeHeatAverage_eq_killed n t ht φ φ.continuous.aestronglyMeasurable] at he
  exact he

theorem bridgeFreeHeat_test_graph_energy (n : ℕ) (t : ℝ) (ht : 0 < t)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ∃ v : unweightedSobolevGraph n,
      unweightedValue n v = bridgeFreeHeatL2 n t ht (unweightedTestToL2 n φ) ∧
      t * ‖unweightedGradient n v‖^2 ≤ ‖unweightedTestToL2 n φ‖^2 -
        ‖bridgeFreeHeatL2 n t ht (unweightedTestToL2 n φ)‖^2 := by
  have hs := bridgeFreeHeatAverage_test_smooth n t φ
  have hL := bridgeFreeHeatAverage_test_memLp n t ht φ
  have hg := bridgeFreeHeatAverage_test_energy n t ht φ
  let v := unweightedSmoothSobolevElement n _ hs hL hg.1
  have hv := unweightedSmoothSobolevElement_value n _ hs hL hg.1
  have hvg := unweightedSmoothSobolevElement_gradient n _ hs hL hg.1
  have hvQ : unweightedValue n v = bridgeFreeHeatL2 n t ht (unweightedTestToL2 n φ) :=
    Lp.ext (hv.trans (bridgeFreeHeatL2_test_coe n t ht φ).symm)
  have hnormG : ‖unweightedGradient n v‖^2 =
      ∫ x, ‖gradient (bridgeFreeHeatAverage n t φ) x‖^2 ∂volume := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae (hvg.fun_comp (fun y => ‖y‖^2))
  have hnormφ : ‖unweightedTestToL2 n φ‖^2 = ∫ x, (φ x)^2 ∂volume := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [unweightedTestToL2_coe n φ] with x hx
    simp only [hx, Real.norm_eq_abs, sq_abs]
  have hnormQ : ‖bridgeFreeHeatL2 n t ht (unweightedTestToL2 n φ)‖^2 =
      ∫ x, (bridgeFreeHeatAverage n t φ x)^2 ∂volume := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [bridgeFreeHeatL2_test_coe n t ht φ] with x hx
    simp only [hx, Real.norm_eq_abs, sq_abs]
  exact ⟨v, hvQ, by rw [hnormG, hnormφ, hnormQ]; exact hg.2⟩

theorem bridgeFreeHeatL2_has_graph_energy (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ v : unweightedSobolevGraph n,
      unweightedValue n v = bridgeFreeHeatL2 n t ht f ∧
      t * ‖unweightedGradient n v‖^2 ≤ ‖f‖^2 - ‖bridgeFreeHeatL2 n t ht f‖^2 := by
  obtain ⟨φ, hφ⟩ := bridge_unweighted_tests_dense n f
  choose v hv henergy using fun k => bridgeFreeHeat_test_graph_energy n t ht (φ k)
  let b : ℕ → ℝ := fun k => (‖unweightedTestToL2 n (φ k)‖^2 -
    ‖bridgeFreeHeatL2 n t ht (unweightedTestToL2 n (φ k))‖^2) / t
  have hQ := ((bridgeFreeHeatL2 n t ht).continuous.tendsto f).comp hφ
  have hb : Tendsto b atTop (𝓝 ((‖f‖^2 - ‖bridgeFreeHeatL2 n t ht f‖^2) / t)) :=
    ((hφ.norm.pow 2).sub (hQ.norm.pow 2)).div_const t
  have hG (k : ℕ) : ‖unweightedGradient n (v k)‖^2 ≤ b k := by
    apply (le_div_iff₀ ht).mpr
    simpa only [mul_comm] using henergy k
  have hvlim : Tendsto (fun k => unweightedValue n (v k)) atTop
      (𝓝 (bridgeFreeHeatL2 n t ht f)) := by simpa only [hv, Function.comp_def] using hQ
  obtain ⟨w, hw, hbound⟩ := bridge_unweighted_graph_limit_energy n v _ b _ hG hb hvlim
  refine ⟨w, hw, ?_⟩
  have h := (le_div_iff₀ ht).mp hbound
  simpa only [mul_comm] using h

end AffineFKProof
