module

public import AffineFK.ConditionalVectorField
public import AffineFK.MatrixHilbertSchmidt
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Positive semidefiniteness of the actual conditional covariance matrix

The covariance is the conditional expectation of the centered outer
product. Conditional positivity and the genuine bilinear pull-out theorem
give its sign and its usual second-moment formula. No covariance sign or
conditional Jensen conclusion is assumed. This is a probabilistic input
to the Ball--Nguyen/Bizeul Hessian projection argument; identification
with the Hessian of an actual marginal remains a separate obligation.

Reuse: Mathlib conditional expectation and bilinear pull-out by Kexing
Ying, Remy Degenne and Etienne Marion; finite-dimensional continuity and
matrix order by Mathlib contributors and Monica Omar (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

def euclideanOuterLinear (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun v :=
    { toFun := fun w i j => v i * w j
      map_add' := by
        intro w z
        ext i j
        change v i * (w + z) j = v i * w j + v i * z j
        rw [PiLp.add_apply]
        ring
      map_smul' := by
        intro c w
        ext i j
        change v i * (c • w) j = c * (v i * w j)
        rw [PiLp.smul_apply]
        simp only [smul_eq_mul]
        ring }
  map_add' := by
    intro v w
    ext z i j
    change (v + w) i * z j = v i * z j + w i * z j
    rw [PiLp.add_apply]
    ring
  map_smul' := by
    intro c v
    ext w i j
    change (c • v) i * w j = c * (v i * w j)
    rw [PiLp.smul_apply]
    simp only [smul_eq_mul]
    ring

def euclideanOuterBilinear (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (((LinearMap.toContinuousLinearMap :
    (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] Matrix (Fin n) (Fin n) ℝ)).toLinearMap).comp
    (euclideanOuterLinear n)).toContinuousLinearMap

theorem euclideanOuterBilinear_apply (n : ℕ) (v w : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) : euclideanOuterBilinear n v w i j = v i * w j := rfl

theorem euclideanOuterBilinear_self_posSemidef (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    (euclideanOuterBilinear n v v).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (fun i : Fin n => v i)
  convert h using 1
  ext i j
  simp [euclideanOuterBilinear_apply, Matrix.vecMulVec_apply]

theorem conditional_covariance_matrix_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : MeasurableSpace Ω) (hs : s ≤ mΩ)
    (n : ℕ) (A : Ω → EuclideanSpace ℝ (Fin n)) (hA : MemLp A 2 μ) :
    let q := condExp s μ A
    (condExp s μ (fun ω => euclideanOuterBilinear n (A ω - q ω) (A ω - q ω))) =ᵐ[μ]
      fun ω => condExp s μ (fun z => euclideanOuterBilinear n (A z) (A z)) ω -
        euclideanOuterBilinear n (q ω) (q ω) := by
  let q := condExp s μ A
  let B := euclideanOuterBilinear n
  have hq : MemLp q 2 μ := hA.condExp (by norm_num)
  have haa : Integrable (fun ω => B (A ω) (A ω)) μ :=
    memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hA hA)
  have hqa : Integrable (fun ω => B (q ω) (A ω)) μ :=
    memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hq hA)
  have haq : Integrable (fun ω => B (A ω) (q ω)) μ :=
    memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hA hq)
  have hqq : Integrable (fun ω => B (q ω) (q ω)) μ :=
    memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hq hq)
  have hqsm : StronglyMeasurable[s] q := stronglyMeasurable_condExp
  have hqqsm : StronglyMeasurable[s] (fun ω => B (q ω) (q ω)) :=
    Continuous.comp_stronglyMeasurable
      (g := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => B p.1 p.2)
      (by fun_prop) (hqsm.prodMk hqsm)
  have hleft := condExp_bilin_of_aestronglyMeasurable_left B hqsm.aestronglyMeasurable hqa
    (hA.integrable (by norm_num))
  have hright := condExp_bilin_of_aestronglyMeasurable_right B hqsm.aestronglyMeasurable haq
    (hA.integrable (by norm_num))
  have hfixed := condExp_of_stronglyMeasurable hs hqqsm hqq
  have heq : (fun ω => B (A ω - q ω) (A ω - q ω)) =
      (((fun ω => B (A ω) (A ω)) - (fun ω => B (q ω) (A ω))) -
        (fun ω => B (A ω) (q ω))) + (fun ω => B (q ω) (q ω)) := by
    funext ω
    ext i j
    simp only [Pi.add_apply, Pi.sub_apply, B, euclideanOuterBilinear_apply,
      PiLp.sub_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  change condExp s μ (fun ω => B (A ω - q ω) (A ω - q ω)) =ᵐ[μ] _
  rw [heq]
  filter_upwards [condExp_add ((haa.sub hqa).sub haq) hqq s,
    condExp_sub (haa.sub hqa) haq s, condExp_sub haa hqa s, hleft, hright]
    with ω hadd hsub hsub' hl hr
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsub']
  simp only [Pi.sub_apply]
  rw [hl, hr, hfixed]
  change ((condExp s μ (fun z => B (A z) (A z)) ω - B (q ω) (q ω)) -
    B (q ω) (q ω)) + B (q ω) (q ω) = _
  abel

theorem conditional_covariance_matrix_posSemidef
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : MeasurableSpace Ω) (hs : s ≤ mΩ)
    (n : ℕ) (A : Ω → EuclideanSpace ℝ (Fin n)) (hA : MemLp A 2 μ) :
    ∀ᵐ ω ∂μ, (condExp s μ (fun z => euclideanOuterBilinear n (A z) (A z)) ω -
      euclideanOuterBilinear n (condExp s μ A ω) (condExp s μ A ω)).PosSemidef := by
  let : MeasurableSpace Ω := mΩ
  have hpos : (0 : Ω → Matrix (Fin n) (Fin n) ℝ) ≤ᵐ[μ]
      fun ω => euclideanOuterBilinear n (A ω - condExp s μ A ω) (A ω - condExp s μ A ω) :=
    Filter.Eventually.of_forall fun ω => (euclideanOuterBilinear_self_posSemidef n _).nonneg
  have hce := condExp_nonneg (m := s) (m₀ := mΩ) (μ := μ) hpos
  filter_upwards [hce, conditional_covariance_matrix_identity μ s hs n A hA] with ω hp heq
  rw [heq] at hp
  exact hp.posSemidef

end AffineFKProof
