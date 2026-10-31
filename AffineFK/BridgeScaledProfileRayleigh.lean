module

public import AffineFK.BridgeProfileRayleigh
public import AffineFK.DirichletLinearEigenvalue

/-!
# The actual original-domain eigenvalue bound from a dilation profile

The proved linear pullback comparison transports the actual H0 Rayleigh
infimum from the bridge domain back to the interior of the original body.
All dilation-radius and summability constants remain explicit.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal Pointwise

set_option backward.isDefEq.respectTransparency false in
theorem bridge_dirichletEigenvalue_interior_le_dilation_profile (n : ℕ) (hn : 0 < n)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D)
    (hconvex : Convex ℝ D) (hzero : 0 ∈ interior D)
    (p α A0 : ℝ) (hp : 2 < p) (hαlower : 1/p < α) (hαupper : α < 1/2) (hA : 0 ≤ A0)
    (hprofile : ∀ t : ℝ, 1 ≤ t →
      -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal ≤ A0 * t^(-p)) :
    dirichletEigenvalue n (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal ((2*bridgeRadius α)^2 *
        (8*(A0/(1-(2 : ℝ)^(1-α*p))) + 4*(n : ℝ)*Real.log 2)) := by
  let c := 2*bridgeRadius α
  have hc : 0 < c := mul_pos (by norm_num) (bridgeRadius_pos α hαupper)
  let A := supportDilationLinearEquiv n c hc.ne'
  let U : Opens (EuclideanSpace ℝ (Fin n)) := ⟨interior D, isOpen_interior⟩
  have himage : dirichletLinearImage n A U = bridgeProfileOpenDomain n D α hαupper := by
    ext x
    change c⁻¹ • x ∈ interior D ↔ x ∈ c • interior D
    rw [mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  have hAnorm : ‖A.toContinuousLinearMap‖ ≤ c := by
    change ‖c • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖ ≤ c
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
    nlinarith
  have hA2 : ‖A.toContinuousLinearMap‖^2 ≤ c^2 :=
    (sq_le_sq₀ (norm_nonneg _) hc.le).mpr hAnorm
  have htrans := dirichletEigenvalue_linear_pullback_le n hn A U
  rw [himage] at htrans
  have hbound := bridge_dirichletEigenvalue_le_dilation_profile n D hcompact hconvex hzero
    p α A0 hp hαlower hαupper hA hprofile
  calc
    _ ≤ ENNReal.ofReal (‖A.toContinuousLinearMap‖^2) *
        dirichletEigenvalue n (bridgeProfileOpenDomain n D α hαupper) := htrans
    _ ≤ ENNReal.ofReal (c^2) * ENNReal.ofReal
        (8*(A0/(1-(2 : ℝ)^(1-α*p))) + 4*(n : ℝ)*Real.log 2) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hA2) hbound
    _ = _ := (ENNReal.ofReal_mul (sq_nonneg c)).symm

end AffineFKProof
