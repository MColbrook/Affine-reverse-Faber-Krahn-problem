module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The actual domain-indicator projection on Lebesgue L2 -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Filter
open scoped RealInnerProductSpace

def gaussianKillL2Value (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  ((Lp.memLp f).indicator hU.nullMeasurableSet).toLp (U.indicator f)

set_option backward.isDefEq.respectTransparency false in
theorem gaussianKillL2Value_coe (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (gaussianKillL2Value n U hU f : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] U.indicator f := by
  unfold gaussianKillL2Value MemLp.toLp
  exact AEEqFun.coeFn_mk _ _

def gaussianKillL2Linear (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun := gaussianKillL2Value n U hU
  map_add' f g := by
    apply Lp.ext
    filter_upwards [gaussianKillL2Value_coe n U hU (f+g),
      Lp.coeFn_add (gaussianKillL2Value n U hU f) (gaussianKillL2Value n U hU g),
      gaussianKillL2Value_coe n U hU f,gaussianKillL2Value_coe n U hU g,Lp.coeFn_add f g]
      with x hsum hadd hf hg hfg
    rw [hsum,hadd]
    simp only [Pi.add_apply]
    rw [hf,hg]
    by_cases hx : x ∈ U
    · simpa only [indicator_of_mem hx,Pi.add_apply] using hfg
    · simp only [indicator_of_notMem hx,add_zero]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [gaussianKillL2Value_coe n U hU (c•f),
      Lp.coeFn_smul c (gaussianKillL2Value n U hU f),
      gaussianKillL2Value_coe n U hU f,Lp.coeFn_smul c f]
      with x hcf hsmul hf hpoint
    simp only [RingHom.id_apply]
    rw [hcf,hsmul]
    simp only [Pi.smul_apply]
    rw [hf]
    by_cases hx : x ∈ U
    · simpa only [indicator_of_mem hx,Pi.smul_apply] using hpoint
    · simp only [indicator_of_notMem hx,smul_zero]

theorem gaussianKillL2Linear_coe (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (gaussianKillL2Linear n U hU f : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] U.indicator f :=
  gaussianKillL2Value_coe n U hU f

theorem gaussianKillL2Linear_norm_le (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖gaussianKillL2Linear n U hU f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [gaussianKillL2Linear_coe n U hU f] with x hx
  rw [hx]
  by_cases hm : x ∈ U
  · rw [indicator_of_mem hm]
  · rw [indicator_of_notMem hm,norm_zero]
    exact norm_nonneg _

def gaussianKillL2 (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (gaussianKillL2Linear n U hU).mkContinuous 1
    (fun f => by simpa only [one_mul] using gaussianKillL2Linear_norm_le n U hU f)

theorem gaussianKillL2_coe (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (gaussianKillL2 n U hU f : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] U.indicator f :=
  gaussianKillL2Linear_coe n U hU f

theorem gaussianKillL2_norm_le (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖gaussianKillL2 n U hU f‖ ≤ ‖f‖ := gaussianKillL2Linear_norm_le n U hU f

theorem gaussianKillL2_inner (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U)
    (f g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ⟪gaussianKillL2 n U hU f,g⟫ = ⟪f,gaussianKillL2 n U hU g⟫ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gaussianKillL2_coe n U hU f,gaussianKillL2_coe n U hU g] with x hf hg
  rw [hf,hg]
  by_cases hx : x ∈ U <;> simp [hx]

theorem gaussianKillL2_of_zero_exterior (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hf : ∀ᵐ x ∂volume, x ∉ U → f x=0) : gaussianKillL2 n U hU f=f := by
  apply Lp.ext
  filter_upwards [gaussianKillL2_coe n U hU f,hf] with x hx hzero
  rw [hx]
  by_cases hm : x ∈ U
  · rw [indicator_of_mem hm]
  · rw [indicator_of_notMem hm,hzero hm]

theorem gaussianKillL2_zero_exterior (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂volume, x ∉ U → gaussianKillL2 n U hU f x=0 := by
  filter_upwards [gaussianKillL2_coe n U hU f] with x hx hm
  rw [hx,indicator_of_notMem hm]

end AffineFKProof
