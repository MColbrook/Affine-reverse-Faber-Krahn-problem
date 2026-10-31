module

public import AffineFK.BridgeScaledProfileRayleigh

/-!
# The full Gaussian-profile bridge eigenvalue lemma

The constant below depends only on p>2. Every stochastic, Gaussian,
Sobolev and variational step has been derived on the actual laws and H0
domain in the imported source chain. The result has the manuscript's full
dimension-free C(p)(A+n) form, with an explicit (nonoptimal) constant.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal Pointwise

def bridgeRayleighConstant (p : ℝ) : ℝ :=
  (2*bridgeRadius ((1/p+1/2)/2))^2 *
    (8/(1-(2 : ℝ)^(1-((1/p+1/2)/2)*p))+4)

theorem bridgeRayleighConstant_pos (p : ℝ) (hp : 2 < p) : 0 < bridgeRayleighConstant p := by
  have hc := bridge_midpoint_choice p hp
  have hR := bridgeRadius_pos _ hc.2
  have hd : 0 < 1-(2 : ℝ)^(1-((1/p+1/2)/2)*p) :=
    sub_pos.mpr (bridge_geometric_ratios p _ hp hc.1 hc.2).1.2
  unfold bridgeRayleighConstant
  positivity

set_option backward.isDefEq.respectTransparency false in
theorem bridge_dirichletEigenvalue_le_profile_constant (p : ℝ) (hp : 2 < p)
    (n : ℕ) (hn : 0 < n)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D)
    (hconvex : Convex ℝ D) (hzero : 0 ∈ interior D)
    (A : ℝ) (hA : 0 ≤ A)
    (hprofile : ∀ t : ℝ, 1 ≤ t →
      -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal ≤ A * t^(-p)) :
    dirichletEigenvalue n (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (bridgeRayleighConstant p * (A+(n : ℝ))) := by
  let α := (1/p+1/2)/2
  let d := 1-(2 : ℝ)^(1-α*p)
  have hc : 1/p < α ∧ α < 1/2 := bridge_midpoint_choice p hp
  have hd : 0 < d := sub_pos.mpr (bridge_geometric_ratios p α hp hc.1 hc.2).1.2
  have h := bridge_dirichletEigenvalue_interior_le_dilation_profile n hn D hcompact hconvex hzero
    p α A hp hc.1 hc.2 hA hprofile
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  change (2*bridgeRadius α)^2 * (8*(A/d)+4*(n : ℝ)*Real.log 2) ≤
    ((2*bridgeRadius α)^2 * (8/d+4)) * (A+(n : ℝ))
  have hl : Real.log 2 ≤ (1 : ℝ) := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog
    exact hlog
  have hlog : 4*(n : ℝ)*Real.log 2 ≤ 4*(n : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 4*(n : ℝ))
  have hcore : 8*(A/d)+4*(n : ℝ)*Real.log 2 ≤ (8/d+4)*(A+(n : ℝ)) := by
    have hz : 0 ≤ 4*A+(8/d)*(n : ℝ) := by positivity
    calc
      _ ≤ 8*(A/d)+4*(n : ℝ) := by linarith
      _ ≤ _ := by
        apply sub_nonneg.mp
        have he : (8/d+4)*(A+(n : ℝ)) - (8*(A/d)+4*(n : ℝ)) =
            4*A+(8/d)*(n : ℝ) := by ring
        rw [he]
        exact hz
  calc
    _ ≤ (2*bridgeRadius α)^2 * ((8/d+4)*(A+(n : ℝ))) :=
      mul_le_mul_of_nonneg_left hcore (sq_nonneg _)
    _ = _ := by ring

end AffineFKProof
