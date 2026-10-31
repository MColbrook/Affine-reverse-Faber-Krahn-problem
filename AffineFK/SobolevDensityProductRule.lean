module

public import AffineFK.UnweightedSobolevIntegration
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The square-density product rule on the actual unweighted H1 graph

A bounded compact test acts continuously on Lebesgue L2. The quadratic
integration-by-parts identity is consequently closed in the value-gradient
Hilbert product. Extending the genuine smooth identity to the completed
graph proves the distributional derivative of f squared without assuming
the desired density identity or global L1 of f itself.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem unweighted_test_mul_memLp (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x => φ x * f x) 2 volume := by
  apply MemLp.of_le_mul (c := ‖TestFunction.toBoundedContinuousFunctionCLM ℝ φ‖) (Lp.memLp f)
    (φ.continuous.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖φ x * f x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((TestFunction.toBoundedContinuousFunctionCLM ℝ φ).norm_coe_le_norm x) (norm_nonneg (f x))

def unweightedTestMultiplyLinear (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun f := (unweighted_test_mul_memLp n φ f).toLp (fun x => φ x * f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (unweighted_test_mul_memLp n φ (f + g)),
      MemLp.coeFn_toLp (unweighted_test_mul_memLp n φ f),
      MemLp.coeFn_toLp (unweighted_test_mul_memLp n φ g),
      Lp.coeFn_add f g,
      Lp.coeFn_add ((unweighted_test_mul_memLp n φ f).toLp _) ((unweighted_test_mul_memLp n φ g).toLp _)]
      with x hfg hf hg ha hb
    rw [hfg, hb]
    simp only [Pi.add_apply]
    rw [hf, hg, ha]
    simp only [Pi.add_apply]
    exact mul_add _ _ _
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (unweighted_test_mul_memLp n φ (c • f)),
      MemLp.coeFn_toLp (unweighted_test_mul_memLp n φ f),
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((unweighted_test_mul_memLp n φ f).toLp _)] with x hcf hf ha hb
    simp only [RingHom.id_apply]
    rw [hcf, hb]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf, ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem unweightedTestMultiplyLinear_coe (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    unweightedTestMultiplyLinear n φ f =ᵐ[volume] fun x => φ x * f x :=
  MemLp.coeFn_toLp (unweighted_test_mul_memLp n φ f)

def unweightedTestMultiply (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (unweightedTestMultiplyLinear n φ).mkContinuous
    ‖TestFunction.toBoundedContinuousFunctionCLM ℝ φ‖ (fun f => by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [unweightedTestMultiplyLinear_coe n φ f] with x hx
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((TestFunction.toBoundedContinuousFunctionCLM ℝ φ).norm_coe_le_norm x) (norm_nonneg (f x)))

theorem unweightedTestMultiply_coe (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    unweightedTestMultiply n φ f =ᵐ[volume] fun x => φ x * f x :=
  unweightedTestMultiplyLinear_coe n φ f

theorem unweighted_weighted_inner (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (f g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ⟪f, unweightedTestMultiply n φ g⟫ = ∫ x, f x * (φ x * g x) := by
  rw [l2_real_inner_integral]
  apply integral_congr_ae
  filter_upwards [unweightedTestMultiply_coe n φ g] with x hx
  rw [hx]

def unweightedSquareTest (n : ℕ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  ⟨(fun x => f x * f x), f.contDiff.mul f.contDiff,
    f.hasCompactSupport.mul_right, Set.subset_univ _⟩

theorem unweightedSquareTest_partial (n : ℕ) (j : Fin n)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n j (unweightedSquareTest n f) x = 2 * (partialTest n j f x * f x) := by
  rw [partialTest_fderiv]
  change fderiv ℝ (fun y => f y * f y) x _ = _
  rw [fderiv_fun_mul (f.contDiff.differentiable (by simp)).differentiableAt
    (f.contDiff.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [← partialTest_fderiv]
  ring

theorem unweighted_smooth_square_product (n : ℕ) (j : Fin n)
    (f φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x) ^ 2 * partialTest n j φ x) =
      -(2 * ∫ x, partialTest n j f x * (φ x * f x)) := by
  have h := test_partial_integration_by_parts n j (unweightedSquareTest n f) φ
  have hl : (∫ x, partialTest n j (unweightedSquareTest n f) x * φ x) =
      2 * ∫ x, partialTest n j f x * (φ x * f x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [unweightedSquareTest_partial]
    ring
  have hr : (∫ x, unweightedSquareTest n f x * partialTest n j φ x) =
      ∫ x, (f x) ^ 2 * partialTest n j φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    change (f x * f x) * _ = _
    ring
  rw [hl, hr] at h
  linarith

theorem unweighted_smooth_square_inner (n : ℕ) (j : Fin n)
    (f φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ⟪unweightedTestToL2 n f,
      unweightedTestMultiply n (partialTest n j φ) (unweightedTestToL2 n f)⟫ =
      -(2 * ⟪l2Coordinate n volume j (unweightedTestToL2 n (testFunctionGradient f)),
        unweightedTestMultiply n φ (unweightedTestToL2 n f)⟫) := by
  rw [← unweighted_partial_toL2, unweighted_weighted_inner, unweighted_weighted_inner]
  have hl : (∫ x, unweightedTestToL2 n f x *
      (partialTest n j φ x * unweightedTestToL2 n f x)) =
      ∫ x, (f x) ^ 2 * partialTest n j φ x := by
    apply integral_congr_ae
    filter_upwards [unweightedTestToL2_coe n f] with x hx
    rw [hx]
    ring
  have hr : (∫ x, unweightedTestToL2 n (partialTest n j f) x *
      (φ x * unweightedTestToL2 n f x)) = ∫ x, partialTest n j f x * (φ x * f x) := by
    apply integral_congr_ae
    filter_upwards [unweightedTestToL2_coe n f,
      unweightedTestToL2_coe n (partialTest n j f)] with x hx hy
    rw [hx, hy]
  rw [hl, hr]
  exact unweighted_smooth_square_product n j f φ

theorem unweighted_graph_square_inner (n : ℕ)
    (v : unweightedSobolevGraph n) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ⟪unweightedValue n v,
      unweightedTestMultiply n (partialTest n j φ) (unweightedValue n v)⟫ =
      -(2 * ⟪l2Coordinate n volume j (unweightedGradient n v),
        unweightedTestMultiply n φ (unweightedValue n v)⟫) := by
  let ν : Measure (EuclideanSpace ℝ (Fin n)) := volume
  let A : SobolevAmbient ν →L[ℝ] Lp ℝ 2 ν :=
    (l2Coordinate n ν j).comp (WithLp.sndL 2 ℝ (Lp ℝ 2 ν) (Lp (EuclideanSpace ℝ (Fin n)) 2 ν))
  let B : SobolevAmbient ν →L[ℝ] Lp ℝ 2 ν :=
    WithLp.fstL 2 ℝ (Lp ℝ 2 ν) (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
  let M := unweightedTestMultiply n φ
  let N := unweightedTestMultiply n (partialTest n j φ)
  have hclosed : IsClosed {w : SobolevAmbient ν |
      ⟪B w, N (B w)⟫ = -(2 * ⟪A w, M (B w)⟫)} :=
    isClosed_eq (B.continuous.inner (N.continuous.comp B.continuous))
      ((continuous_const.mul (A.continuous.inner (M.continuous.comp B.continuous))).neg)
  have hincl : ((unweightedSmoothPair n).range : Set (SobolevAmbient ν)) ⊆
      {w : SobolevAmbient ν | ⟪B w, N (B w)⟫ = -(2 * ⟪A w, M (B w)⟫)} := by
    rintro w ⟨f, rfl⟩
    exact unweighted_smooth_square_inner n j f φ
  exact (closure_minimal hincl hclosed) v.property

theorem unweighted_graph_square_product_rule (n : ℕ)
    (v : unweightedSobolevGraph n) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (unweightedValue n v x) ^ 2 * partialTest n j φ x) =
      -(∫ x, (2 * unweightedValue n v x * (unweightedGradient n v x) j) * φ x) := by
  have h := unweighted_graph_square_inner n v j φ
  rw [unweighted_weighted_inner, unweighted_weighted_inner] at h
  have hl : (∫ x, unweightedValue n v x *
      (partialTest n j φ x * unweightedValue n v x)) =
      ∫ x, (unweightedValue n v x) ^ 2 * partialTest n j φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hr : (2 * ∫ x, l2Coordinate n volume j (unweightedGradient n v) x *
      (φ x * unweightedValue n v x)) =
      ∫ x, (2 * unweightedValue n v x * (unweightedGradient n v x) j) * φ x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [l2Coordinate_coe n volume j (unweightedGradient n v)] with x hx
    rw [hx]
    ring
  rwa [hl, hr] at h

end AffineFKProof
