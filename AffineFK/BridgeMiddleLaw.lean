module

public import AffineFK.BridgeMiddleCovariance
public import AffineFK.BridgeScaledBridgeLaw

/-!
# The actual split-bridge construction has the full centered bridge law

The two shorter bridges and the Gaussian middle point are genuinely
independent under their explicit product probability. Their constructed
continuous path has the actual full bridge law, proved from all Gaussian
finite-dimensional means and covariances and the Borel path-space theorem.
No conditional-law, covariance, or bridge-splitting identity is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridgeSplitCenteredPath_hasLaw (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    HasLaw (bridgeSplitCenteredPath n s t hs ht) (bridgeScaledBridgeLaw n (s+t) (add_pos hs ht))
      (bridgeMiddleMeasure n) := by
  refine ⟨(bridgeSplitCenteredPath_measurable n s t hs ht).aemeasurable, ?_⟩
  apply bridge_gaussian_continuous_image_law_ext n (bridgeMiddleMeasure n)
    (bridgeSplitCenteredPath n s t hs ht) (bridgeSplitCenteredPath_measurable n s t hs ht)
    (bridgeScaledBridgeLaw n (s+t) (add_pos hs ht))
    (bridgeSplitCenteredPath_gaussian_process n s t hs ht)
    (bridgeScaledBridgeLaw_gaussian_process n (s+t) (add_pos hs ht))
  · intro r i
    exact (bridgeSplitCenteredPath_mean n s t hs ht (r,i)).trans
      (bridgeScaledBridgeLaw_coordinate_mean n (s+t) (add_pos hs ht) r i).symm
  · intro r u i j
    exact (bridgeSplitCenteredPath_bridge_covariance n s t hs ht (r,i) (u,j)).trans
      (bridgeScaledBridgeLaw_coordinate_covariance n (s+t) (add_pos hs ht) r u i j).symm

end AffineFKProof
