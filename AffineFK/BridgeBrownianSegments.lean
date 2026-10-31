module

public import AffineFK.BridgeScaledBrownianLaw
public import AffineFK.BridgeGaussianPathLawExt
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# Past paths and future increment paths of the actual finite Brownian law

The split occurs at the genuine time `s` in the interval `[0,s+t]`.
The future path has its initial value subtracted. Both whole paths are
measurable random variables in their Borel continuous-path spaces.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

def bridgePastTime (s t : ℝ) (ht : 0 ≤ t) (r : Icc (0 : ℝ) s) : Icc (0 : ℝ) (s+t) :=
  ⟨r, r.2.1, r.2.2.trans (le_add_of_nonneg_right ht)⟩

def bridgeFutureTime (s t : ℝ) (hs : 0 ≤ s) (r : Icc (0 : ℝ) t) : Icc (0 : ℝ) (s+t) :=
  ⟨s+r, add_nonneg hs r.2.1, by have := r.2.2; linarith⟩

def bridgeSplitTime (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : Icc (0 : ℝ) (s+t) :=
  ⟨s, hs, le_add_of_nonneg_right ht⟩

def bridgePastPath (n : ℕ) (s t : ℝ) (ht : 0 ≤ t)
    (f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n))) :
    C(Icc (0 : ℝ) s, EuclideanSpace ℝ (Fin n)) where
  toFun r := f (bridgePastTime s t ht r)
  continuous_toFun := f.continuous.comp (continuous_subtype_val.subtype_mk _)

def bridgeFutureIncrementPath (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n))) :
    C(Icc (0 : ℝ) t, EuclideanSpace ℝ (Fin n)) where
  toFun r := f (bridgeFutureTime s t hs r) - f (bridgeSplitTime s t hs ht)
  continuous_toFun := (f.continuous.comp
    ((continuous_const.add continuous_subtype_val).subtype_mk _)).sub continuous_const

theorem bridgePastPath_measurable (n : ℕ) (s t : ℝ) (ht : 0 ≤ t) :
    Measurable (bridgePastPath n s t ht) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  exact ContinuousMap.measurable_eval (bridgePastTime s t ht r)

theorem bridgeFutureIncrementPath_measurable (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Measurable (bridgeFutureIncrementPath n s t hs ht) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  exact (ContinuousMap.measurable_eval (bridgeFutureTime s t hs r)).sub
    (ContinuousMap.measurable_eval (bridgeSplitTime s t hs ht))

theorem bridge_indepFun_of_comap {Ω A B C D : Type*} [MeasurableSpace Ω]
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    [mC : MeasurableSpace C] [mD : MeasurableSpace D]
    (μ : Measure Ω) (f : Ω → A) (g : Ω → B) (F : A → C) (G : B → D)
    (hA : mA = mC.comap F) (hB : mB = mD.comap G)
    (h : IndepFun (F ∘ f) (G ∘ g) μ) : IndepFun f g μ := by
  rw [IndepFun_iff_Indep] at h ⊢
  rwa [hA, hB, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]

end AffineFKProof
