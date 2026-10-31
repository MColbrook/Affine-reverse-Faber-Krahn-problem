module

public import AffineFK.ConvolutionDensityProduct
public import AffineFK.ConditionalVectorField
public import AffineFK.OrdinaryWeakScoreSobolevSmooth
public import AffineFK.VectorTestUniqueness

/-!
# The actual conditional score of an independent normalized affine sum

One measurable field is chosen before all compact tests. The genuine
input-density product identities prove its output weak equation; compact
uniqueness then identifies the actual smooth logarithmic score. The
output density and its actual affine-image law are explicit hypotheses
here; the OU commutation application supplies them separately.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff

def convolutionScoreCombination (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  a • gradient (fun x => Real.log (ρ₁ x)) p.1 + b • gradient (fun x => Real.log (ρ₂ x)) p.2

theorem convolutionScoreCombination_memLp (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 2 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 2 (densityMeasure n ρ₂)) (a b : ℝ) :
    MemLp (convolutionScoreCombination n ρ₁ ρ₂ a b) 2 ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)) :=
  ((hs₁.comp_fst _).const_smul a).add ((hs₂.comp_snd _).const_smul b)

theorem convolution_score_conditional_identification (n : ℕ)
    (ρ₁ ρ₂ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 2 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 2 (densityMeasure n ρ₂))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (hlaw : ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2) = densityMeasure n ρ) :
    let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
    let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun p => a • p.1 + b • p.2
    let m := (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧ MemLp r 2 (densityMeasure n ρ) ∧
      (∀ p, r (W p) = condExp m μ (convolutionScoreCombination n ρ₁ ρ₂ a b) p) ∧
      (r =ᵐ[densityMeasure n ρ] gradient (fun x => Real.log (ρ x))) ∧
      MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ) ∧
      (fun p => gradient (fun x => Real.log (ρ x)) (W p)) =ᵐ[μ]
        condExp m μ (convolutionScoreCombination n ρ₁ ρ₂ a b) := by
  let E := EuclideanSpace ℝ (Fin n)
  let mΩ : MeasurableSpace (E × E) := inferInstance
  let ν := densityMeasure n ρ₁
  let η := densityMeasure n ρ₂
  let μ := ν.prod η
  let W : E × E → E := fun p => a • p.1 + b • p.2
  let S := convolutionScoreCombination n ρ₁ ρ₂ a b
  let m := (inferInstance : MeasurableSpace E).comap W
  let : MeasurableSpace (E × E) := mΩ
  have hW : Measurable W := by dsimp [W]; fun_prop
  let : IsProbabilityMeasure (μ.map W) := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let : IsProbabilityMeasure (densityMeasure n ρ) := by rw [← hlaw]; infer_instance
  have hS : MemLp S 2 μ := convolutionScoreCombination_memLp n ρ₁ ρ₂ hs₁ hs₂ a b
  obtain ⟨r, hr, hr2, hrep, _henergy, hpair⟩ := scaled_conditional_vector_field μ n S hS W hW 1
  have hrep' (p : E × E) : r (W p) = condExp m μ S p := by simpa only [one_smul] using hrep p
  have hweak (i : Fin n) (φ : 𝓓((⊤ : Opens E), ℝ)) :
      (∫ x, r x i * φ x ∂μ.map W) = -(∫ x, partialTest n i φ x ∂μ.map W) := by
    let F := singleComponentTest n i φ
    have hF : MemLp F 2 (μ.map W) :=
      (Lp.memLp (testFunctionToL2 (μ.map W) F)).ae_eq (testFunctionToL2_coe (μ.map W) F)
    have hp := hpair F F.continuous.stronglyMeasurable hF
    dsimp only [F] at hp
    simp_rw [singleComponentTest_inner_at] at hp
    have hL₁ := integrable_fst_mul_test_comp n ν η
      (fun x => gradient (fun y => Real.log (ρ₁ y)) x i) ((hs₁.eval_piLp i).integrable (by norm_num))
      W (by dsimp [W]; fun_prop) φ
    have hL₂ := integrable_snd_mul_test_comp n ν η
      (fun x => gradient (fun y => Real.log (ρ₂ y)) x i) ((hs₂.eval_piLp i).integrable (by norm_num))
      W (by dsimp [W]; fun_prop) φ
    have hcalc : (∫ p, S p i * φ (W p) ∂μ) =
        a * (∫ p, gradient (fun x => Real.log (ρ₁ x)) p.1 i * φ (W p) ∂μ) +
        b * (∫ p, gradient (fun x => Real.log (ρ₂ x)) p.2 i * φ (W p) ∂μ) := by
      calc
        _ = ∫ p, a * (gradient (fun x => Real.log (ρ₁ x)) p.1 i * φ (W p)) +
            b * (gradient (fun x => Real.log (ρ₂ x)) p.2 i * φ (W p)) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun p => by
            dsimp only [S, convolutionScoreCombination]
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            ring
        _ = _ := by
          rw [integral_add (f := fun p => a * (gradient (fun x => Real.log (ρ₁ x)) p.1 i * φ (W p)))
            (g := fun p => b * (gradient (fun x => Real.log (ρ₂ x)) p.2 i * φ (W p)))
              (hL₁.const_mul a) (hL₂.const_mul b), integral_const_mul, integral_const_mul]
    have hfirst : (∫ p, gradient (fun x => Real.log (ρ₁ x)) p.1 i * φ (W p) ∂μ) =
        -a * (∫ p, partialTest n i φ (W p) ∂μ) :=
      smooth_density_convolution_first_fst n ρ₁ hρ₁ hpos₁ η hs₁ i a b ha φ
    have hsecond : (∫ p, gradient (fun x => Real.log (ρ₂ x)) p.2 i * φ (W p) ∂μ) =
        -b * (∫ p, partialTest n i φ (W p) ∂μ) :=
      smooth_density_convolution_first_snd n ν ρ₂ hρ₂ hpos₂ hs₂ i a b hb φ
    calc
      _ = ∫ p, S p i * φ (W p) ∂μ := by simpa only [one_mul] using hp.2.2
      _ = -(∫ p, partialTest n i φ (W p) ∂μ) := by
        rw [hcalc, hfirst, hsecond]
        calc
          _ = -(a ^ 2 + b ^ 2) * (∫ p, partialTest n i φ (W p) ∂μ) := by ring
          _ = _ := by rw [hab, neg_one_mul]
      _ = _ := by
        congr 1
        exact (integral_map hW.aemeasurable (partialTest n i φ).continuous.aestronglyMeasurable).symm
  have hrρ : MemLp r 2 (densityMeasure n ρ) := by rw [← hlaw]; exact hr2
  have hweakρ (i : Fin n) (φ : 𝓓((⊤ : Opens E), ℝ)) :
      (∫ x, r x i * φ x ∂densityMeasure n ρ) = -(∫ x, partialTest n i φ x ∂densityMeasure n ρ) := by
    rw [← hlaw]
    exact hweak i φ
  have hid := ordinaryWeakScore_smooth_identification n ρ hρ hpos r hrρ hweakρ
  have hidmap : r =ᵐ[μ.map W] gradient (fun x => Real.log (ρ x)) := by rw [hlaw]; exact hid.1
  have hpull : (fun p => gradient (fun x => Real.log (ρ x)) (W p)) =ᵐ[μ] condExp m μ S := by
    filter_upwards [ae_of_ae_map hW.aemeasurable hidmap] with p hp
    exact hp.symm.trans (hrep' p)
  exact ⟨r, hr, hrρ, hrep', hid.1, hid.2.1, hpull⟩

end AffineFKProof
