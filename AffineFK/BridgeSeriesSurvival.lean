module

public import AffineFK.BridgeContinuousPath

/-!
# An actual continuous-series survival probability

The law here is the proved independent Gaussian coefficient-series law.
It has not yet been identified as the standard Brownian-bridge law.
The event that the entire continuous path remains in `2 R interior D`
is genuinely open in path space and measurable. No killed heat kernel,
variational eigenvalue or Brownian-law identification is a hypothesis
or conclusion of these source-development results.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology

def bridgeRadius (a : ℝ) : ℝ := 1 / (2 * (1 - (2 : ℝ) ^ (a - 1 / 2)))

theorem bridgeRadius_pos (a : ℝ) (ha : a < 1 / 2) : 0 < bridgeRadius a := by
  unfold bridgeRadius
  have h := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ))
    (show a - 1 / 2 < 0 by linarith)
  positivity

theorem gauge_le_mem_double_interior (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hconvex : Convex ℝ D) (hzero : 0 ∈ interior D)
    (R : ℝ) (hR : 0 < R) (x : EuclideanSpace ℝ (Fin n)) (hx : gauge D x ≤ R) :
    x ∈ (2 * R) • interior D := by
  have hR2 : 0 < 2 * R := by positivity
  have hnhds : D ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) := mem_interior_iff_mem_nhds.mp hzero
  have hscaled : gauge D ((2 * R)⁻¹ • x) < 1 := by
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hR2.le), smul_eq_mul]
    calc
      _ ≤ (2 * R)⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR2.le)
      _ = (1 / 2 : ℝ) := by field_simp
      _ < 1 := by norm_num
  have hmem := (gauge_lt_one_iff_mem_interior hconvex hnhds).mp hscaled
  refine ⟨(2 * R)⁻¹ • x, hmem, ?_⟩
  change (2 * R) • ((2 * R)⁻¹ • x) = x
  rw [smul_smul, mul_inv_cancel₀ hR2.ne', one_smul]

def bridgeSeriesSurvivalEvent (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n))) (a : ℝ) :
    Set C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) :=
  {f | ∀ t : Icc (0 : ℝ) 1, f t ∈ (2 * bridgeRadius a) • interior D}

theorem bridgeSeriesSurvivalEvent_isOpen (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (a : ℝ) (ha : a < 1 / 2) :
    IsOpen (bridgeSeriesSurvivalEvent n D a) := by
  have hR : 2 * bridgeRadius a ≠ 0 := ne_of_gt (mul_pos (by norm_num) (bridgeRadius_pos a ha))
  simpa only [bridgeSeriesSurvivalEvent, Set.MapsTo, Set.mem_univ, forall_true_left] using
    (ContinuousMap.isOpen_setOfPred_mapsTo (X := Icc (0 : ℝ) 1) isCompact_univ
      (isOpen_interior.smul₀ hR))

/-- The exact exponential survival lower bound for the actual continuous
coefficient-series law. Brownian identification is explicitly separate. -/
theorem bridgeSeriesSurvival_probability_lower
    (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D)
    (hconvex : Convex ℝ D) (hzero : 0 ∈ interior D)
    (p a A : ℝ) (hp : 2 < p) (ha : 1 / p < a) (hupper : a < 1 / 2) (hA : 0 ≤ A)
    (hprofile : ∀ t : ℝ, 1 ≤ t →
      -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal ≤ A * t ^ (-p)) :
    ENNReal.ofReal (Real.exp (-A / (1 - (2 : ℝ) ^ (1 - a * p)))) ≤
      bridgeSeriesLaw n (bridgeSeriesSurvivalEvent n D a) := by
  apply (bridgeSeriesLaw_radius_lower n D hcompact hconvex hzero p a A hp ha hupper hA hprofile).trans
  apply measure_mono
  intro f hf t
  exact gauge_le_mem_double_interior n D hconvex hzero (bridgeRadius a)
    (bridgeRadius_pos a hupper) (f t) (hf t)

end AffineFKProof
