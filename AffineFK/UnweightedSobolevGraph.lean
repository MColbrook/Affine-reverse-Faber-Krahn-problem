module

public import AffineFK.WeightedTestIntegration
public import AffineFK.L2Coordinates
public import Mathlib.Topology.Sequences
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The actual H1 completion over infinite Lebesgue volume

Compact support, not finite total volume, places every test and its
gradient in L2. Their value-gradient pairs generate a closed Hilbert
submodule. This construction does not instantiate a finite-volume
weighted Sobolev graph. Mathlib test functions, Lp spaces, Hilbert
products and topological closures retain their primary attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

def unweightedTestToL2 (n : ℕ) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), F) →ₗ[ℝ]
      Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun φ := (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ
  map_add' φ ψ := by
    exact MemLp.toLp_add
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
      (ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport)
  map_smul' c φ := by
    exact MemLp.toLp_const_smul c
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

theorem unweightedTestToL2_coe (n : ℕ) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), F)) :
    unweightedTestToL2 n φ =ᵐ[volume] φ :=
  MemLp.coeFn_toLp (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

def unweightedSmoothPair (n : ℕ) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) →ₗ[ℝ]
      SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))).symm.toLinearEquiv.toLinearMap.comp
      ((unweightedTestToL2 n).prod
        ((unweightedTestToL2 n).comp testFunctionGradient.toLinearMap))

def unweightedSobolevGraph (n : ℕ) :
    Submodule ℝ (SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  (unweightedSmoothPair n).range.topologicalClosure

theorem unweightedSobolevGraph_isClosed (n : ℕ) :
    IsClosed (unweightedSobolevGraph n :
      Set (SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n))))) :=
  Submodule.isClosed_topologicalClosure _

instance unweightedSobolevGraph_completeSpace (n : ℕ) :
    CompleteSpace (unweightedSobolevGraph n) :=
  (unweightedSobolevGraph_isClosed n).completeSpace_coe

def unweightedValue (n : ℕ) : unweightedSobolevGraph n →L[ℝ]
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (WithLp.fstL 2 ℝ _ _).comp (unweightedSobolevGraph n).subtypeL

def unweightedGradient (n : ℕ) : unweightedSobolevGraph n →L[ℝ]
    Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (WithLp.sndL 2 ℝ _ _).comp (unweightedSobolevGraph n).subtypeL

theorem unweighted_smooth_pair_mem (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    unweightedSmoothPair n φ ∈ unweightedSobolevGraph n :=
  (unweightedSmoothPair n).range.le_topologicalClosure ⟨φ, rfl⟩

theorem unweighted_graph_norm_sq (n : ℕ) (v : unweightedSobolevGraph n) :
    ‖v‖ ^ 2 = ‖unweightedValue n v‖ ^ 2 + ‖unweightedGradient n v‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

theorem unweighted_approximating_tests (n : ℕ) (v : unweightedSobolevGraph n) :
    ∃ φ : ℕ → 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      Tendsto (fun k => unweightedTestToL2 n (φ k)) atTop (𝓝 (unweightedValue n v)) ∧
      Tendsto (fun k => unweightedTestToL2 n (testFunctionGradient (φ k)))
        atTop (𝓝 (unweightedGradient n v)) := by
  obtain ⟨w, hw, hlimit⟩ := mem_closure_iff_seq_limit.mp v.property
  choose φ hφ using hw
  have hpair : Tendsto (fun k => unweightedSmoothPair n (φ k)) atTop
      (𝓝 (v : SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    simpa only [hφ] using hlimit
  refine ⟨φ, ?_, ?_⟩
  · exact ((WithLp.fstL 2 ℝ _ _).continuous.tendsto _).comp hpair
  · exact ((WithLp.sndL 2 ℝ _ _).continuous.tendsto _).comp hpair

end AffineFKProof
