module

public import AffineFK.UnweightedSobolevGraph
public import AffineFK.PoincareSmoothExtension

/-!
# Smooth Lebesgue L2 functions in the actual unweighted H1 graph

The genuine cutoff sequence converges in both Lebesgue L2 components.
Its integrable dominators are f squared and a fixed linear combination
of f squared and the gradient norm squared, so finite total volume is
unnecessary. The generic L2 dominated-convergence and pointwise cutoff
lemmas are reused with attribution from the independently developed
PoincareSmoothExtension module; no Poincare premise or probability
instance is used here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology ContDiff

theorem unweighted_smooth_mem_graph (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hL2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hgradL2 : MemLp (gradient f) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    WithLp.toLp 2 (hL2.toLp f, hgradL2.toLp (gradient f)) ∈ unweightedSobolevGraph n := by
  let ν : Measure (EuclideanSpace ℝ (Fin n)) := volume
  obtain ⟨χ, hχ, hinner, _, M, hM0, hM⟩ := exists_smooth_unit_cutoff n
  have hχ0 : χ 0 = 1 := hinner 0 (by simp)
  have hvalue : Tendsto (fun k => unweightedTestToL2 n (poincareSmoothCutoff n f hf χ k)) atTop
      (𝓝 (hL2.toLp f)) := by
    apply poincareSmoothExtension_L2_tendsto ν _ _
      (fun k => (poincareSmoothCutoff n f hf χ k : EuclideanSpace ℝ (Fin n) → ℝ)) f
      (fun k => unweightedTestToL2_coe n _) hL2.coeFn_toLp (fun x => (f x) ^ 2)
    · simpa only [Real.norm_eq_abs, sq_abs] using
        (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
    · exact fun k => Eventually.of_forall fun x => (poincareSmoothCutoff_bounds n f hf χ hχ M hM0 hM k x).1
    · exact Eventually.of_forall fun x => (poincareSmoothCutoff_pointwise n f hf χ hχ0 M hM x).1
  have hgradient : Tendsto (fun k => unweightedTestToL2 n
      (testFunctionGradient (poincareSmoothCutoff n f hf χ k))) atTop
      (𝓝 (hgradL2.toLp (gradient f))) := by
    apply poincareSmoothExtension_L2_tendsto ν _ _
      (fun k => gradient (poincareSmoothCutoff n f hf χ k)) (gradient f)
      (fun k => (unweightedTestToL2_coe n _).trans
        (Eventually.of_forall fun x => testFunctionGradient_apply _ x)) hgradL2.coeFn_toLp
      (fun x => 2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * (f x) ^ 2)
    · have hi := (memLp_two_iff_integrable_sq_norm hgradL2.aestronglyMeasurable).mp hgradL2
      have hf2 : Integrable (fun x => (f x) ^ 2) ν := by
        simpa only [Real.norm_eq_abs, sq_abs] using
          (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
      exact (hi.const_mul 2).add (hf2.const_mul (2 * M ^ 2))
    · exact fun k => Eventually.of_forall fun x => (poincareSmoothCutoff_bounds n f hf χ hχ M hM0 hM k x).2
    · exact Eventually.of_forall fun x => (poincareSmoothCutoff_pointwise n f hf χ hχ0 M hM x).2
  have hpair : Tendsto (fun k => unweightedSmoothPair n (poincareSmoothCutoff n f hf χ k)) atTop
      (𝓝 (WithLp.toLp 2 (hL2.toLp f, hgradL2.toLp (gradient f)))) := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 ν)
      (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)).symm.continuous.tendsto _).comp
        (hvalue.prodMk_nhds hgradient)
  exact (unweightedSobolevGraph_isClosed n).mem_of_tendsto hpair
    (Eventually.of_forall fun k => unweighted_smooth_pair_mem n _)

def unweightedSmoothSobolevElement (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hL2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hgradL2 : MemLp (gradient f) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    unweightedSobolevGraph n :=
  ⟨WithLp.toLp 2 (hL2.toLp f, hgradL2.toLp (gradient f)),
    unweighted_smooth_mem_graph n f hf hL2 hgradL2⟩

theorem unweightedSmoothSobolevElement_value (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hL2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hgradL2 : MemLp (gradient f) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    unweightedValue n (unweightedSmoothSobolevElement n f hf hL2 hgradL2) =ᵐ[volume] f :=
  hL2.coeFn_toLp

theorem unweightedSmoothSobolevElement_gradient (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hL2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hgradL2 : MemLp (gradient f) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    unweightedGradient n (unweightedSmoothSobolevElement n f hf hL2 hgradL2) =ᵐ[volume] gradient f :=
  hgradL2.coeFn_toLp

theorem unweighted_smooth_has_graph (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hL2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hgradL2 : MemLp (gradient f) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ v : unweightedSobolevGraph n,
      (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] f ∧
      (unweightedGradient n v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        gradient f :=
  ⟨unweightedSmoothSobolevElement n f hf hL2 hgradL2,
    unweightedSmoothSobolevElement_value n f hf hL2 hgradL2,
    unweightedSmoothSobolevElement_gradient n f hf hL2 hgradL2⟩

end AffineFKProof
