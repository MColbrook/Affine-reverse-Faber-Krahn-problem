module

public import AffineFK.DirichletMultiplier
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Compactly supported global H1 elements belong to the actual H0 domain

A genuine compact smooth cutoff equals one on the support. Its bounded
H1 multiplier maps every global compact smooth core function into the
domain's compact smooth core. Continuity and actual value-map injectivity
then prove H0 membership; no boundary trace theorem is assumed.

The smooth separation theorem is Mathlib's partition-of-unity construction
by Sebastien Gouezel and contributors, with its original attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter Set
open scoped Distributions ContDiff RealInnerProductSpace Topology

theorem exists_dirichlet_compact_cutoff (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ (U : Set _)) :
    ∃ χ : 𝓓(U, ℝ), (∀ x ∈ K, χ x = 1) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖gradient (χ : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ≤ M := by
  obtain ⟨V, hVopen, hKV, hVU, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure hK U.isOpen hKU
  obtain ⟨f, hf, hfrange, hfsupport, hfone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hVopen hK.isClosed hKV
  have hfsupp : tsupport f ⊆ (U : Set (EuclideanSpace ℝ (Fin n))) := by
    rw [tsupport, hfsupport]
    exact hVU
  have hfcompact : HasCompactSupport f := by
    change IsCompact (closure (Function.support f))
    rw [hfsupport]
    exact hVcompact
  let χ : 𝓓(U, ℝ) := ⟨f, hf, hfcompact, hfsupp⟩
  let χtop := dirichletTestToTop n U χ
  let G : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    TestFunction.toBoundedContinuousFunctionCLM ℝ (testFunctionGradient χtop)
  refine ⟨χ, (fun x hx => (hfone x).mp hx), ?_, ‖G‖, norm_nonneg _, ?_⟩
  · intro x
    exact hfrange (mem_range_self x)
  · intro x
    have hG : G x = gradient (χ : EuclideanSpace ℝ (Fin n) → ℝ) x :=
      testFunctionGradient_apply χtop x
    rw [← hG]
    exact G.norm_coe_le_norm x

set_option maxHeartbeats 1000000 in
theorem h1Multiplier_image_in_dirichlet (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m)
    (hmsupp : tsupport m ⊆ (U : Set (EuclideanSpace ℝ (Fin n))))
    (C0 C1 : ℝ) (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (v : unweightedSobolevGraph n) :
    h1Multiplier n m hm C0 C1 hb0 hb1 v ∈ dirichletSobolev n U := by
  let L := h1Multiplier n m hm C0 C1 hb0 hb1
  obtain ⟨φ, hφ, hgφ⟩ := unweighted_approximating_tests n v
  let vk : ℕ → unweightedSobolevGraph n := fun k =>
    ⟨unweightedSmoothPair n (φ k), unweighted_smooth_pair_mem n (φ k)⟩
  have hpair : Tendsto (fun k => unweightedSmoothPair n (φ k)) atTop (𝓝 v.val) := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))).symm.continuous.tendsto _).comp
        (hφ.prodMk_nhds hgφ)
  have hlim : Tendsto vk atTop (𝓝 v) := tendsto_subtype_rng.mpr hpair
  have hcore (k : ℕ) : L (vk k) ∈ dirichletSobolev n U := by
    let ψ : 𝓓(U, ℝ) := ⟨fun x => m x * φ k x, hm.mul (φ k).contDiff,
      (φ k).hasCompactSupport.mul_left, tsupport_mul_subset_left.trans hmsupp⟩
    change L (dirichletTestToH1 n ⊤ (φ k)) ∈ dirichletSobolev n U
    rw [h1Multiplier_dirichlet_test]
    exact dirichlet_test_mem n U ψ
  exact (dirichletSobolev_isClosed n U).mem_of_tendsto
    ((L.continuous.tendsto v).comp hlim) (Eventually.of_forall hcore)

theorem unweighted_mem_dirichlet_of_compact_support (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKU : K ⊆ (U : Set _))
    (v : unweightedSobolevGraph n)
    (hsupp : ∀ᵐ x ∂volume, x ∉ K → unweightedValue n v x = 0) :
    v ∈ dirichletSobolev n U := by
  obtain ⟨χ, hχone, hχrange, M, hM, hχgrad⟩ := exists_dirichlet_compact_cutoff n U K hK hKU
  have hχbound (x) : ‖χ x‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
    exact (hχrange x).2
  let L := h1Multiplier n (χ : EuclideanSpace ℝ (Fin n) → ℝ) χ.contDiff 1 M hχbound hχgrad
  have hmem := h1Multiplier_image_in_dirichlet n U (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    χ.contDiff χ.tsupport_subset 1 M hχbound hχgrad v
  have hval : unweightedValue n (L v) = unweightedValue n v := by
    apply Lp.ext
    filter_upwards [h1Multiplier_value n _ χ.contDiff 1 M hχbound hχgrad v, hsupp] with x hx hs
    rw [hx]
    by_cases hxK : x ∈ K
    · rw [hχone x hxK, one_mul]
    · rw [hs hxK, mul_zero]
  have heq : L v = v := unweighted_sobolev_value_injective n hval
  rwa [heq] at hmem

end AffineFKProof
