module

public import AffineFK.WhitenedConvolutionIsotropy
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Symmetry and convex support of the actual whitened sum

Independence is represented by the actual product law. Negation commutes
with addition and the linear whitening map. Convexity places each sum in
twice the original body; the measurable image then gives the almost-sure
support of precisely the same output law used for covariance and Fisher
information.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped Pointwise

def whitenedSupportBody (n : ℕ) (η : Measure (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun x => (2 : ℝ) • Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (covarianceWhiteningMatrix n (convolutionCovarianceMatrix n α η)) x) '' K

theorem whitenedSumLaw_neg_invariant (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    [Measure.IsNegInvariant ν] [Measure.IsNegInvariant η] (α : ℝ) :
    Measure.IsNegInvariant (whitenedSumLaw n ν η α) := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ := ν.prod η
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (covarianceWhiteningMatrix n (convolutionCovarianceMatrix n α η))
  let W : E × E → E := fun p => T (p.1 + p.2)
  have hW : Measurable W := by dsimp only [W]; fun_prop
  have hneg : μ.map Neg.neg = μ := by
    change (ν.prod η).map (Prod.map Neg.neg Neg.neg) = _
    rw [← Measure.map_prod_map ν η measurable_neg measurable_neg,
      Measure.map_neg_eq_self, Measure.map_neg_eq_self]
  constructor
  change (μ.map W).map Neg.neg = μ.map W
  calc
    _ = μ.map (Neg.neg ∘ W) := Measure.map_map measurable_neg hW
    _ = μ.map (W ∘ Neg.neg) := by
      congr 1
      funext p
      change -(T (p.1 + p.2)) = T (-p.1 + -p.2)
      rw [← neg_add, map_neg]
    _ = (μ.map Neg.neg).map W := (Measure.map_map hW measurable_neg).symm
    _ = _ := by rw [hneg]

theorem whitenedSupportBody_compact_convex (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K) :
    IsCompact (whitenedSupportBody n η α K) ∧ Convex ℝ (whitenedSupportBody n η α K) := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (covarianceWhiteningMatrix n (convolutionCovarianceMatrix n α η))
  have heq : whitenedSupportBody n η α K = ((2 : ℝ) • T).toLinearMap '' K := rfl
  rw [heq]
  exact ⟨hK.image ((2 : ℝ) • T).continuous, hconv.linear_image _⟩

theorem whitenedSupportBody_even (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : ∀ x, -x ∈ K ↔ x ∈ K) :
    ∀ z, -z ∈ whitenedSupportBody n η α K ↔ z ∈ whitenedSupportBody n η α K := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (covarianceWhiteningMatrix n (convolutionCovarianceMatrix n α η))
  intro z
  constructor
  · rintro ⟨x, hx, heq⟩
    change (2 : ℝ) • T x = -z at heq
    refine ⟨-x, (hK x).mpr hx, ?_⟩
    change (2 : ℝ) • T (-x) = z
    rw [map_neg, smul_neg, heq, neg_neg]
  · rintro ⟨x, hx, heq⟩
    change (2 : ℝ) • T x = z at heq
    refine ⟨-x, (hK x).mpr hx, ?_⟩
    change (2 : ℝ) • T (-x) = -z
    rw [map_neg, smul_neg, heq]

theorem whitenedSumLaw_support (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hν : ∀ᵐ x ∂ν, x ∈ K) (hη : ∀ᵐ x ∂η, x ∈ K) (α : ℝ) :
    ∀ᵐ z ∂whitenedSumLaw n ν η α, z ∈ whitenedSupportBody n η α K := by
  let E := EuclideanSpace ℝ (Fin n)
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (covarianceWhiteningMatrix n (convolutionCovarianceMatrix n α η))
  let W : E × E → E := fun p => T (p.1 + p.2)
  have hW : Measurable W := by dsimp only [W]; fun_prop
  have hD : MeasurableSet (whitenedSupportBody n η α K) :=
    ((whitenedSupportBody_compact_convex n η α K hK hconv).1).measurableSet
  have hp : ∀ᵐ p ∂ν.prod η, p.1 ∈ K ∧ p.2 ∈ K := by
    apply (Measure.ae_prod_iff_ae_ae ((hK.measurableSet.preimage measurable_fst).inter
      (hK.measurableSet.preimage measurable_snd))).mpr
    filter_upwards [hν] with x hx
    filter_upwards [hη] with y hy
    exact ⟨hx, hy⟩
  apply (ae_map_iff hW.aemeasurable hD).mpr
  filter_upwards [hp] with p hp
  have hmid : (1 / 2 : ℝ) • p.1 + (1 / 2 : ℝ) • p.2 ∈ K :=
    hconv hp.1 hp.2 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨(1 / 2 : ℝ) • p.1 + (1 / 2 : ℝ) • p.2, hmid, ?_⟩
  change (2 : ℝ) • T ((1 / 2 : ℝ) • p.1 + (1 / 2 : ℝ) • p.2) = T (p.1 + p.2)
  simp only [map_add, map_smul, smul_add, smul_smul]
  norm_num

end AffineFKProof
