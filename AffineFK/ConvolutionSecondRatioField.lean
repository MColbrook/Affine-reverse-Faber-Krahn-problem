module

public import AffineFK.ConvolutionSecondRatioProduct
public import AffineFK.MatrixEntryLp
public import AffineFK.GaussianSecondDensityRatioConditional

/-!
# The actual conditional second-density-ratio matrix of a convolution

One matrix field is chosen before every coordinate and compact test.
The normalized product identities determine its actual output second
density ratios by compact uniqueness. Operator-norm matrix L2 is genuine
finite-dimensional L2; no Hilbert--Schmidt norm substitution is used.
The smooth positive output density and its true affine-image law are
explicit analytic inputs, supplied separately in the OU application.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Matrix
open scoped Distributions ContDiff Matrix.Norms.L2Operator

def densitySecondRatioMatrix (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => secondDensityRatio n ρ i j x

theorem convolutionSecondRatioCombination_memLp (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂))
    (hq₁ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₁ i j) 2 (densityMeasure n ρ₁))
    (hq₂ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₂ i j) 2 (densityMeasure n ρ₂))
    (a b : ℝ) :
    MemLp (convolutionSecondRatioCombination n ρ₁ ρ₂ a b) 2
      ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)) := by
  apply matrix_memLp_two_of_entries
  exact convolutionSecondRatioCombination_entry_memLp n ρ₁ ρ₂ hs₁ hs₂ hq₁ hq₂ a b

theorem convolution_second_ratio_conditional_identification (n : ℕ)
    (ρ₁ ρ₂ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂))
    (hq₁ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₁ i j) 2 (densityMeasure n ρ₁))
    (hq₂ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₂ i j) 2 (densityMeasure n ρ₂))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (hlaw : ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2) = densityMeasure n ρ) :
    let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
    let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun p => a • p.1 + b • p.2
    let m := (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W
    ∃ q : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ,
      StronglyMeasurable q ∧ MemLp q 2 (densityMeasure n ρ) ∧
      (∀ p, q (W p) = condExp m μ (convolutionSecondRatioCombination n ρ₁ ρ₂ a b) p) ∧
      (q =ᵐ[densityMeasure n ρ] densitySecondRatioMatrix n ρ) ∧
      MemLp (densitySecondRatioMatrix n ρ) 2 (densityMeasure n ρ) ∧
      (fun p => densitySecondRatioMatrix n ρ (W p)) =ᵐ[μ]
        condExp m μ (convolutionSecondRatioCombination n ρ₁ ρ₂ a b) := by
  let E := EuclideanSpace ℝ (Fin n)
  let mΩ : MeasurableSpace (E × E) := inferInstance
  let ν := densityMeasure n ρ₁
  let η := densityMeasure n ρ₂
  let μ := ν.prod η
  let W : E × E → E := fun p => a • p.1 + b • p.2
  let R := convolutionSecondRatioCombination n ρ₁ ρ₂ a b
  let m := (inferInstance : MeasurableSpace E).comap W
  let : MeasurableSpace (E × E) := mΩ
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hm : m ≤ mΩ := hW.comap_le
  let : IsProbabilityMeasure (μ.map W) := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let : IsProbabilityMeasure (densityMeasure n ρ) := by rw [← hlaw]; infer_instance
  have hR : MemLp R 2 μ := convolutionSecondRatioCombination_memLp n ρ₁ ρ₂ hs₁ hs₂ hq₁ hq₂ a b
  obtain ⟨q, hq, hq2, hrep⟩ := conditional_expectation_factor μ R hR W hW
  have hqρ : MemLp q 2 (densityMeasure n ρ) := by rw [← hlaw]; exact hq2
  have hentry (i j : Fin n) : MemLp (fun x => q x i j) 2 (densityMeasure n ρ) := by
    simpa only [Function.comp_def, matrixEntryContinuousLinear_apply] using
      (matrixEntryContinuousLinear n i j).comp_memLp' hqρ
  have hweak (i j : Fin n) (φ : 𝓓((⊤ : Opens E), ℝ)) :
      (∫ x, q x i j * φ x ∂densityMeasure n ρ) =
        ∫ x, partialTest n i (partialTest n j φ) x ∂densityMeasure n ρ := by
    have hφ2 : MemLp φ 2 (μ.map W) := testFunction_memLp_two n (μ.map W) φ
    have hφW : MemLp (fun p => φ (W p)) 2 μ := (hasLaw_map hW.aemeasurable).memLp_fun_comp hφ2
    have hRij : MemLp (fun p => R p i j) 2 μ := by
      simpa only [Function.comp_def, matrixEntryContinuousLinear_apply] using
        (matrixEntryContinuousLinear n i j).comp_memLp' hR
    have hprod : Integrable (fun p => R p i j * φ (W p)) μ := hRij.integrable_mul hφW
    have hWs : @Measurable (E × E) E m inferInstance W := measurable_iff_comap_le.mpr le_rfl
    have hφm : AEStronglyMeasurable[m] (fun p => φ (W p)) μ :=
      (φ.continuous.stronglyMeasurable.comp_measurable hWs).aestronglyMeasurable
    have hp := conditional_bilinear_pairing μ m hm (ContinuousLinearMap.mul ℝ ℝ)
      (fun p => R p i j) (hRij.integrable (by norm_num)) (fun p => φ (W p)) hφm hprod
    have hcomm := conditional_matrix_entry μ m n R hR i j
    have hqij : StronglyMeasurable (fun x => q x i j) :=
      (matrixEntryContinuousLinear n i j).continuous.comp_stronglyMeasurable hq
    rw [← hlaw]
    calc
      _ = ∫ p, q (W p) i j * φ (W p) ∂μ :=
        integral_map hW.aemeasurable (hqij.mul φ.continuous.stronglyMeasurable).aestronglyMeasurable
      _ = ∫ p, condExp m μ (fun z => R z i j) p * φ (W p) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcomm] with p hp
        rw [hrep p, hp]
      _ = ∫ p, R p i j * φ (W p) ∂μ := hp.2
      _ = ∫ p, partialTest n i (partialTest n j φ) (W p) ∂μ :=
        convolutionSecondRatioCombination_test_identity n ρ₁ ρ₂ hρ₁ hpos₁ hρ₂ hpos₂
          hs₁ hs₂ hq₁ hq₂ a b ha hb hab i j φ
      _ = _ := (integral_map hW.aemeasurable
        (partialTest n i (partialTest n j φ)).continuous.aestronglyMeasurable).symm
  have hid (i j : Fin n) : (fun x => q x i j) =ᵐ[densityMeasure n ρ] secondDensityRatio n ρ i j :=
    (secondDensityRatio_identified_by_test_identity n ρ hρ hpos i j _ (hentry i j) (hweak i j)).1
  have hEq : q =ᵐ[densityMeasure n ρ] densitySecondRatioMatrix n ρ := by
    filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hid i j] with x hx
    ext i j
    exact hx i j
  have hEqMap : q =ᵐ[μ.map W] densitySecondRatioMatrix n ρ := by rw [hlaw]; exact hEq
  have hpull : (fun p => densitySecondRatioMatrix n ρ (W p)) =ᵐ[μ] condExp m μ R := by
    filter_upwards [ae_of_ae_map hW.aemeasurable hEqMap] with p hp
    exact hp.symm.trans (hrep p)
  exact ⟨q, hq, hqρ, hrep, hEq, hqρ.ae_eq hEq, hpull⟩

end AffineFKProof
