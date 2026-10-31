module

public import AffineFK.UnweightedSobolevGraph
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Distributional derivatives of the unweighted H1 completion

The compact-test integration-by-parts identity extends to the actual
closed value-gradient graph over Lebesgue volume. Local integrability,
which follows from L2 on finite-volume neighbourhoods, suffices for
distributional separation. No finite total volume is assumed.

The separation theorem is due to Sebastien Gouezel in Mathlib's
Analysis.Distribution.AEEqOfIntegralContDiff. The Hilbert-product closure
argument follows the independently checked weighted construction, with
the genuine compact-support Lebesgue L2 map replacing its finite-measure map.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem unweighted_partial_toL2 (n : ℕ) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    unweightedTestToL2 n (partialTest n j φ) =
      l2Coordinate n volume j (unweightedTestToL2 n (testFunctionGradient φ)) := by
  apply Lp.ext
  filter_upwards [unweightedTestToL2_coe n (partialTest n j φ),
    l2Coordinate_coe n volume j (unweightedTestToL2 n (testFunctionGradient φ)),
    unweightedTestToL2_coe n (testFunctionGradient φ)] with x hp hc hg
  rw [hp, hc, hg, testFunctionGradient_apply, partialTest_apply]

theorem unweighted_test_inner_integration_by_parts (n : ℕ) (j : Fin n)
    (f φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ⟪l2Coordinate n volume j (unweightedTestToL2 n (testFunctionGradient f)),
      unweightedTestToL2 n φ⟫ =
      -⟪unweightedTestToL2 n f, unweightedTestToL2 n (partialTest n j φ)⟫ := by
  rw [← unweighted_partial_toL2, l2_real_inner_integral, l2_real_inner_integral]
  have hleft : (∫ x, unweightedTestToL2 n (partialTest n j f) x *
      unweightedTestToL2 n φ x) = ∫ x, partialTest n j f x * φ x := by
    apply integral_congr_ae
    filter_upwards [unweightedTestToL2_coe n (partialTest n j f),
      unweightedTestToL2_coe n φ] with x hx hy
    rw [hx, hy]
  have hright : (∫ x, unweightedTestToL2 n f x *
      unweightedTestToL2 n (partialTest n j φ) x) = ∫ x, f x * partialTest n j φ x := by
    apply integral_congr_ae
    filter_upwards [unweightedTestToL2_coe n f,
      unweightedTestToL2_coe n (partialTest n j φ)] with x hx hy
    rw [hx, hy]
  rw [hleft, hright]
  exact test_partial_integration_by_parts n j f φ

theorem unweighted_graph_integration_by_parts (n : ℕ)
    (v : unweightedSobolevGraph n) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ⟪l2Coordinate n volume j (unweightedGradient n v), unweightedTestToL2 n φ⟫ =
      -⟪unweightedValue n v, unweightedTestToL2 n (partialTest n j φ)⟫ := by
  let ν : Measure (EuclideanSpace ℝ (Fin n)) := volume
  let A : SobolevAmbient ν →L[ℝ] Lp ℝ 2 ν :=
    (l2Coordinate n ν j).comp (WithLp.sndL 2 ℝ (Lp ℝ 2 ν) (Lp (EuclideanSpace ℝ (Fin n)) 2 ν))
  let B : SobolevAmbient ν →L[ℝ] Lp ℝ 2 ν :=
    WithLp.fstL 2 ℝ (Lp ℝ 2 ν) (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
  let a := unweightedTestToL2 n φ
  let b := unweightedTestToL2 n (partialTest n j φ)
  have hclosed : IsClosed {w : SobolevAmbient ν | ⟪A w, a⟫ = -⟪B w, b⟫} :=
    isClosed_eq (A.continuous.inner continuous_const)
      ((B.continuous.inner continuous_const).neg)
  have hincl : ((unweightedSmoothPair n).range : Set (SobolevAmbient ν)) ⊆
      {w : SobolevAmbient ν | ⟪A w, a⟫ = -⟪B w, b⟫} := by
    rintro w ⟨f, rfl⟩
    exact unweighted_test_inner_integration_by_parts n j f φ
  exact (closure_minimal hincl hclosed) v.property

theorem unweighted_l2_eq_zero_of_inner_test_zero (n : ℕ)
    (g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (h : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      ⟪g, unweightedTestToL2 n φ⟫ = 0) : g = 0 := by
  have hg : LocallyIntegrable (fun x => g x) volume :=
    (Lp.memLp g).locallyIntegrable (by norm_num)
  have hae : ∀ᵐ x ∂volume, g x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hg
    intro ψ hψ hsupp
    let φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
      ⟨ψ, hψ, hsupp, Set.subset_univ _⟩
    have hφ := h φ
    rw [l2_real_inner_integral] at hφ
    calc
      _ = ∫ x, g x * unweightedTestToL2 n φ x := by
        apply integral_congr_ae
        filter_upwards [unweightedTestToL2_coe n φ] with x hx
        change ψ x * g x = g x * unweightedTestToL2 n φ x
        rw [hx]
        change ψ x * g x = g x * ψ x
        exact mul_comm _ _
      _ = 0 := hφ
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))]
    with x hx hz
  rw [hx, hz]
  rfl

theorem unweighted_gradient_zero_of_value_zero (n : ℕ)
    (v : unweightedSobolevGraph n) (hv : unweightedValue n v = 0) :
    unweightedGradient n v = 0 := by
  have hcoord (j : Fin n) : l2Coordinate n volume j (unweightedGradient n v) = 0 := by
    apply unweighted_l2_eq_zero_of_inner_test_zero n
    intro φ
    rw [unweighted_graph_integration_by_parts n v j φ, hv, inner_zero_left, neg_zero]
  have hnorm : ‖unweightedGradient n v‖ ^ 2 = 0 := by
    rw [← l2Coordinate_norm_sq_sum n volume]
    simp only [hcoord, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (unweightedGradient n v)]

theorem unweighted_sobolev_value_injective (n : ℕ) :
    Function.Injective (unweightedValue n) := by
  intro v w hvw
  have hval : unweightedValue n (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hgrad := unweighted_gradient_zero_of_value_zero n (v - w) hval
  have hnorm := unweighted_graph_norm_sq n (v - w)
  simp only [hval, hgrad, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hnorm
  have hz : v - w = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v - w)])
  exact sub_eq_zero.mp hz

end AffineFKProof
