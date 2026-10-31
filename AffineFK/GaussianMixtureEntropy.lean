module

public import AffineFK.GaussianSmoothingDensity
public import AffineFK.GaussianReferenceScore
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# A joint reference measure for Gaussian mixtures

The law of (U,aU+bG), on the actual independent product space, is obtained
by weighting nu times standard Gaussian with the explicit conditional
Gaussian density ratio. Projection then uses Mathlib's proved data
processing inequality (Remy Degenne and Lorenzo Luccioli, Apache-2.0).
No mixture convexity or finiteness of relative entropy is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ContDiff

def gaussianJointAffineMap (n : ℕ) (a b : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  (p.1, a • p.1 + b • p.2)

def gaussianJointRatio (n : ℕ) (a b : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : ℝ :=
  (b ^ n)⁻¹ * standardGaussianDensity n (b⁻¹ • (p.2 - a • p.1)) /
    standardGaussianDensity n p.2

theorem gaussianJointRatio_continuous (n : ℕ) (a b : ℝ) :
    Continuous (gaussianJointRatio n a b) := by
  unfold gaussianJointRatio
  exact (continuous_const.mul ((standardGaussianDensity_smooth n).continuous.comp
    (by fun_prop))).div ((standardGaussianDensity_smooth n).continuous.comp continuous_snd)
      (fun p => (standardGaussianDensity_pos n p.2).ne')

theorem gaussianJointRatio_pos (n : ℕ) (a b : ℝ) (hb : 0 < b)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    0 < gaussianJointRatio n a b p :=
  div_pos (mul_pos (inv_pos.mpr (pow_pos hb n)) (standardGaussianDensity_pos n _))
    (standardGaussianDensity_pos n _)

theorem gaussian_joint_affine_withDensity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (gaussianJointAffineMap n a b) =
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).withDensity
        (fun p => ENNReal.ofReal (gaussianJointRatio n a b p)) := by
  have hT : Measurable (gaussianJointAffineMap n a b) := by unfold gaussianJointAffineMap; fun_prop
  have hR := (gaussianJointRatio_continuous n a b).measurable.ennreal_ofReal
  have hk := (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hT, lintegral_withDensity_eq_lintegral_mul _ hR hf]
  change (∫⁻ p, (f ∘ gaussianJointAffineMap n a b) p
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) = _
  rw [lintegral_prod (f ∘ gaussianJointAffineMap n a b) (hf.comp hT).aemeasurable,
    lintegral_prod ((fun p => ENNReal.ofReal (gaussianJointRatio n a b p)) * f)
      (hR.mul hf).aemeasurable]
  apply lintegral_congr
  intro u
  have hfu : Measurable (fun x : EuclideanSpace ℝ (Fin n) => f (u, x)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  change (∫⁻ g, f (u, a • u + b • g) ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = _
  rw [gaussianSmoothingDensity_affine_lintegral n a b hb u _ hfu,
    stdGaussian_eq_densityMeasure n, densityMeasure]
  have hRu : Measurable (fun x => ENNReal.ofReal (gaussianJointRatio n a b (u, x))) :=
    hR.comp (measurable_const.prodMk measurable_id)
  change _ = ∫⁻ x, ((fun y => ENNReal.ofReal (gaussianJointRatio n a b (u, y))) *
    (fun y => f (u, y))) x ∂(volume.withDensity (fun x => ENNReal.ofReal (standardGaussianDensity n x)))
  rw [lintegral_withDensity_eq_lintegral_mul _ hk (hRu.mul hfu)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  have hc : ENNReal.ofReal (standardGaussianDensity n x) *
      ENNReal.ofReal (gaussianJointRatio n a b (u, x)) =
      ENNReal.ofReal ((b ^ n)⁻¹) *
        ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • u))) := by
    rw [← ENNReal.ofReal_mul (standardGaussianDensity_pos n x).le,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hb.le n))]
    congr 1
    unfold gaussianJointRatio
    dsimp only
    field_simp [(standardGaussianDensity_pos n x).ne']
  rw [← mul_assoc, ← hc, mul_assoc]
  rfl

theorem gaussian_joint_affine_ac (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (gaussianJointAffineMap n a b) ≪
      ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [gaussian_joint_affine_withDensity n ν a b hb]
  exact withDensity_absolutelyContinuous _ _

theorem gaussian_mixture_klDiv_le_joint (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (a b : ℝ) :
    klDiv ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      klDiv ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (gaussianJointAffineMap n a b)) (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  have hT : Measurable (gaussianJointAffineMap n a b) := by unfold gaussianJointAffineMap; fun_prop
  have h := klDiv_map_le
    ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (gaussianJointAffineMap n a b))
    (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) measurable_snd
  rw [Measure.map_map measurable_snd hT, Measure.map_snd_prod] at h
  simpa only [Function.comp_def, gaussianJointAffineMap, measure_univ, one_smul] using h

end AffineFKProof
