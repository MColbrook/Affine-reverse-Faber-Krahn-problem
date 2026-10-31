module

public import AffineFK.BridgeMiddleLaw
public import AffineFK.BridgeKilledKernelJoint
public import Mathlib.Tactic.Module

/-!
# Actual affine endpoint bridges and the split Gaussian middle point

These are pointwise continuous-path identities. The actual law of the
centered middle construction is already proved separately; no conditional
distribution or desired survival-factorization identity is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

/-- The affine bridge from x to z obtained by adding its linear endpoint
interpolation to a centered continuous path on `[0,T]`. -/
def bridgeAffineCenteredPath (n : ℕ) (T : ℝ) (x z : EuclideanSpace ℝ (Fin n))
    (f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n))) :
    C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) where
  toFun r := x+f r+((r:ℝ)/T) • (z-x)
  continuous_toFun := by fun_prop

theorem bridgeAffineCenteredPath_measurable (n : ℕ) (T : ℝ) (x z : EuclideanSpace ℝ (Fin n)) :
    Measurable (bridgeAffineCenteredPath n T x z) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  exact (measurable_const.add (ContinuousMap.measurable_eval r)).add measurable_const

/-- The actual affine Gaussian middle point: mean x+s/(s+t)(z-x) and
centered fluctuation sqrt(s*t/(s+t)) times the independent standard vector. -/
def bridgeSplitMiddlePoint (n : ℕ) (s t : ℝ) (x z w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  x+(s/(s+t)) • (z-x)+bridgeMiddleScale s t • w

theorem bridgeSplitMiddlePoint_measurable (n : ℕ) (s t : ℝ) (x z : EuclideanSpace ℝ (Fin n)) :
    Measurable (bridgeSplitMiddlePoint n s t x z) := by
  unfold bridgeSplitMiddlePoint
  fun_prop

theorem bridgeMiddleAffinePath_left (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x z : EuclideanSpace ℝ (Fin n)) (p : BridgeMiddleSample n)
    (r : Icc (0 : ℝ) (s+t)) (hr : (r:ℝ) ≤ s) :
    bridgeAffineCenteredPath n (s+t) x z (bridgeSplitCenteredPath n s t hs ht p) r =
      bridgeEndpointBridgePath n s x (bridgeSplitMiddlePoint n s t x z p.2)
        (bridgeContinuousSeries n p.1.1) (bridgeUnitTime s hs ⟨r,r.2.1,hr⟩) := by
  change x+bridgeSplitCenteredPath n s t hs ht p r+((r:ℝ)/(s+t)) • (z-x) = _
  rw [bridgeSplitCenteredPath_left n s t hs ht p r hr]
  change x+(Real.sqrt s • bridgeContinuousSeries n p.1.1 (bridgeUnitTime s hs ⟨r,r.2.1,hr⟩)+
    ((r:ℝ)/s) • (bridgeMiddleScale s t • p.2))+((r:ℝ)/(s+t)) • (z-x) =
    x+Real.sqrt s • bridgeContinuousSeries n p.1.1 (bridgeUnitTime s hs ⟨r,r.2.1,hr⟩)+
      ((r:ℝ)/s) • (bridgeSplitMiddlePoint n s t x z p.2-x)
  have hm : bridgeSplitMiddlePoint n s t x z p.2-x =
      (s/(s+t)) • (z-x)+bridgeMiddleScale s t • p.2 := by
    unfold bridgeSplitMiddlePoint
    abel
  have hc : ((r:ℝ)/s)*(s/(s+t)) = (r:ℝ)/(s+t) := by field_simp
  have hv : ((r:ℝ)/s) • (bridgeSplitMiddlePoint n s t x z p.2-x) =
      ((r:ℝ)/(s+t)) • (z-x)+((r:ℝ)/s) • (bridgeMiddleScale s t • p.2) := by
    rw [hm, smul_add, smul_smul, hc]
  rw [hv]
  abel

theorem bridgeMiddleAffinePath_right (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x z : EuclideanSpace ℝ (Fin n)) (p : BridgeMiddleSample n)
    (r : Icc (0 : ℝ) (s+t)) (hr : s ≤ (r:ℝ)) :
    bridgeAffineCenteredPath n (s+t) x z (bridgeSplitCenteredPath n s t hs ht p) r =
      bridgeEndpointBridgePath n t (bridgeSplitMiddlePoint n s t x z p.2) z
        (bridgeContinuousSeries n p.1.2) (bridgePostUnitTime s t ht ⟨r,hr,r.2.2⟩) := by
  let u : ℝ := ((r:ℝ)-s)/t
  let c : ℝ := s/(s+t)
  let W := bridgeMiddleScale s t • p.2
  let β := Real.sqrt t • bridgeContinuousSeries n p.1.2 (bridgePostUnitTime s t ht ⟨r,hr,r.2.2⟩)
  change x+bridgeSplitCenteredPath n s t hs ht p r+((r:ℝ)/(s+t)) • (z-x) = _
  rw [bridgeSplitCenteredPath_right n s t hs ht p r hr]
  change x+(β+(1-u) • W)+((r:ℝ)/(s+t)) • (z-x) =
    bridgeSplitMiddlePoint n s t x z p.2+β+u • (z-bridgeSplitMiddlePoint n s t x z p.2)
  have hm : bridgeSplitMiddlePoint n s t x z p.2 = x+c • (z-x)+W := rfl
  have hd : z-bridgeSplitMiddlePoint n s t x z p.2 = (1-c) • (z-x)-W := by
    rw [hm]
    module
  have hc : c+u*(1-c) = (r:ℝ)/(s+t) := by
    dsimp [c,u]
    field_simp [ht.ne', (add_pos hs ht).ne']
    ring
  calc
    _ = x+β+(1-u) • W+(c+u*(1-c)) • (z-x) := by rw [hc]; abel
    _ = _ := by rw [hd,hm]; module

end AffineFKProof
