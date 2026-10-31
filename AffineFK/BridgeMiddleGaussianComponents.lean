module

public import AffineFK.BridgeMiddleMeasurable
public import AffineFK.BridgeIndependentGaussianSum

/-!
# Independent Gaussian components of the actual middle-point construction

The inactive short-bridge component is multiplied by zero. Arbitrary time
indices may therefore be sent to a fixed endpoint in that component;
no measurability or Gaussian assertion about the desired whole law is
assumed in this representation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

/-- The first normalized bridge time, with zero as an unused time after
the splitting point. Its coefficient is then zero. -/
def bridgeMiddleFirstTime (s t : ℝ) (hs : 0 < s) (r : Icc (0 : ℝ) (s+t)) : Icc (0 : ℝ) 1 :=
  if h : (r:ℝ) ≤ s then bridgeUnitTime s hs ⟨r,r.2.1,h⟩ else ⟨0,by norm_num⟩

/-- The second normalized bridge time, with zero as an unused time before
the splitting point. Its coefficient is then zero. -/
def bridgeMiddleSecondTime (s t : ℝ) (ht : 0 < t) (r : Icc (0 : ℝ) (s+t)) : Icc (0 : ℝ) 1 :=
  if h : (r:ℝ) ≤ s then ⟨0,by norm_num⟩ else bridgePostUnitTime s t ht ⟨r,le_of_not_ge h,r.2.2⟩

/-- First short-bridge amplitude, zero on the second interval. -/
def bridgeMiddleFirstFactor (s : ℝ) (r : ℝ) : ℝ := if r ≤ s then Real.sqrt s else 0

/-- Second short-bridge amplitude, zero on the first interval. -/
def bridgeMiddleSecondFactor (s t : ℝ) (r : ℝ) : ℝ := if r ≤ s then 0 else Real.sqrt t

/-- The piecewise linear coefficient connecting the middle point to zero
at both outer endpoints. -/
def bridgeMiddleLinearCoefficient (s t : ℝ) (r : ℝ) : ℝ :=
  if r ≤ s then r/s else 1-(r-s)/t

/-- Scalar coordinate process of the first actual independent short bridge. -/
def bridgeMiddleFirstProcess (n : ℕ) (s t : ℝ) (hs : 0 < s)
    (q : Icc (0 : ℝ) (s+t) × Fin n)
    (ω : ∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n)) : ℝ :=
  bridgeMiddleFirstFactor s q.1 * bridgeContinuousSeries n ω (bridgeMiddleFirstTime s t hs q.1) q.2

/-- Scalar coordinate process of the second actual independent short bridge. -/
def bridgeMiddleSecondProcess (n : ℕ) (s t : ℝ) (ht : 0 < t)
    (q : Icc (0 : ℝ) (s+t) × Fin n)
    (ω : ∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n)) : ℝ :=
  bridgeMiddleSecondFactor s t q.1 * bridgeContinuousSeries n ω (bridgeMiddleSecondTime s t ht q.1) q.2

/-- Scalar coordinate process of the actual independent Gaussian middle
point, with variance `s*t/(s+t)` and the exact linear interpolation. -/
def bridgeMiddleEndpointProcess (n : ℕ) (s t : ℝ)
    (q : Icc (0 : ℝ) (s+t) × Fin n) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (bridgeMiddleLinearCoefficient s t q.1 * bridgeMiddleScale s t) * z q.2

theorem bridgeMiddleFirstProcess_gaussian (n : ℕ) (s t : ℝ) (hs : 0 < s) :
    IsGaussianProcess (bridgeMiddleFirstProcess n s t hs) (bridgeCoefficientMeasure n) :=
  ((bridgeContinuousSeries_gaussian_process n).comp_right
    (fun q : Icc (0 : ℝ) (s+t) × Fin n => (bridgeMiddleFirstTime s t hs q.1,q.2))).smul
      (fun q : Icc (0 : ℝ) (s+t) × Fin n => bridgeMiddleFirstFactor s (q.1:ℝ))

theorem bridgeMiddleSecondProcess_gaussian (n : ℕ) (s t : ℝ) (ht : 0 < t) :
    IsGaussianProcess (bridgeMiddleSecondProcess n s t ht) (bridgeCoefficientMeasure n) :=
  ((bridgeContinuousSeries_gaussian_process n).comp_right
    (fun q : Icc (0 : ℝ) (s+t) × Fin n => (bridgeMiddleSecondTime s t ht q.1,q.2))).smul
      (fun q : Icc (0 : ℝ) (s+t) × Fin n => bridgeMiddleSecondFactor s t (q.1:ℝ))

theorem bridgeMiddleEndpointProcess_gaussian (n : ℕ) (s t : ℝ) :
    IsGaussianProcess (bridgeMiddleEndpointProcess n s t) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  classical
  constructor
  intro I
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi
    (fun q => (bridgeMiddleLinearCoefficient s t q.1.1 * bridgeMiddleScale s t) •
      coordinateFunctional n q.1.2)
  convert (IsGaussian.hasGaussianLaw_id
    (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))).map L using 1
  ext z q
  simp [bridgeMiddleEndpointProcess, L, coordinateFunctional_apply]

theorem bridgeSplitCenteredPath_components (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (p : BridgeMiddleSample n) (q : Icc (0 : ℝ) (s+t) × Fin n) :
    bridgeSplitCenteredPath n s t hs ht p q.1 q.2 =
      (bridgeMiddleFirstProcess n s t hs q p.1.1 + bridgeMiddleSecondProcess n s t ht q p.1.2) +
        bridgeMiddleEndpointProcess n s t q p.2 := by
  by_cases hr : (q.1:ℝ) ≤ s
  · rw [bridgeSplitCenteredPath_left n s t hs ht p q.1 hr]
    change Real.sqrt s * bridgeContinuousSeries n p.1.1 (bridgeUnitTime s hs ⟨q.1,q.1.2.1,hr⟩) q.2 +
      ((q.1:ℝ)/s)*(bridgeMiddleScale s t*p.2 q.2) = _
    simp [bridgeMiddleFirstProcess, bridgeMiddleSecondProcess, bridgeMiddleEndpointProcess,
      bridgeMiddleFirstFactor, bridgeMiddleSecondFactor, bridgeMiddleLinearCoefficient,
      bridgeMiddleFirstTime, hr, mul_assoc]
  · rw [bridgeSplitCenteredPath_right n s t hs ht p q.1 (le_of_not_ge hr)]
    change Real.sqrt t * bridgeContinuousSeries n p.1.2
      (bridgePostUnitTime s t ht ⟨q.1,le_of_not_ge hr,q.1.2.2⟩) q.2 +
      (1-((q.1:ℝ)-s)/t)*(bridgeMiddleScale s t*p.2 q.2) = _
    simp [bridgeMiddleFirstProcess, bridgeMiddleSecondProcess, bridgeMiddleEndpointProcess,
      bridgeMiddleFirstFactor, bridgeMiddleSecondFactor, bridgeMiddleLinearCoefficient,
      bridgeMiddleSecondTime, hr, mul_assoc]

theorem bridgeSplitCenteredPath_gaussian_process (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    IsGaussianProcess (fun q : Icc (0 : ℝ) (s+t) × Fin n =>
      fun p : BridgeMiddleSample n => bridgeSplitCenteredPath n s t hs ht p q.1 q.2)
      (bridgeMiddleMeasure n) := by
  have hfirst := bridge_gaussian_process_prod_sum (bridgeCoefficientMeasure n) (bridgeCoefficientMeasure n)
    (bridgeMiddleFirstProcess n s t hs) (bridgeMiddleSecondProcess n s t ht)
    (bridgeMiddleFirstProcess_gaussian n s t hs) (bridgeMiddleSecondProcess_gaussian n s t ht)
  have hall := bridge_gaussian_process_prod_sum
    ((bridgeCoefficientMeasure n).prod (bridgeCoefficientMeasure n))
    (stdGaussian (EuclideanSpace ℝ (Fin n))) _ (bridgeMiddleEndpointProcess n s t)
    hfirst (bridgeMiddleEndpointProcess_gaussian n s t)
  exact hall.congr (fun q => Filter.Eventually.of_forall
    (fun p => (bridgeSplitCenteredPath_components n s t hs ht p q).symm))

end AffineFKProof
