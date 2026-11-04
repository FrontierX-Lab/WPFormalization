import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-! The locally finite diffuse length intensity with cumulative mass b².
It is the square-root pushforward of Lebesgue measure on [0,∞), hence the
ordinary intensity denoted 2t dt on the nonnegative half-line. -/
noncomputable section
namespace WP.RandomGeometry
open MeasureTheory Set
open scoped ENNReal NNReal Topology

def quadraticLengthIntensity : Measure ℝ≥0 :=
  Measure.map (fun x : ℝ => NNReal.sqrt (Real.toNNReal x))
    (volume.restrict (Ici 0))

lemma quadraticLengthIntensity_map_measurable :
    Measurable (fun x : ℝ => NNReal.sqrt (Real.toNNReal x)) :=
  (NNReal.continuous_sqrt.comp continuous_real_toNNReal).measurable

lemma quadraticLengthIntensity_Iic (b : ℝ≥0) :
    quadraticLengthIntensity (Iic b)=ENNReal.ofReal ((b : ℝ)^2) := by
  rw [quadraticLengthIntensity,Measure.map_apply quadraticLengthIntensity_map_measurable
    measurableSet_Iic,Measure.restrict_apply
      (quadraticLengthIntensity_map_measurable measurableSet_Iic)]
  have he : (fun x : ℝ => NNReal.sqrt (Real.toNNReal x)) ⁻¹' Iic b ∩ Ici 0 =
      Icc 0 ((b : ℝ)^2) := by
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_Iic,mem_Ici,mem_Icc,
      NNReal.sqrt_le_iff_le_sq,Real.toNNReal_le_iff_le_coe,NNReal.coe_pow]
    exact and_comm
  rw [he,Real.volume_Icc,sub_zero]

lemma quadraticLengthIntensity_Ioc (a b : ℝ≥0) :
    quadraticLengthIntensity (Ioc a b)=ENNReal.ofReal ((b : ℝ)^2-(a : ℝ)^2) := by
  rw [quadraticLengthIntensity,Measure.map_apply quadraticLengthIntensity_map_measurable
    measurableSet_Ioc,Measure.restrict_apply
      (quadraticLengthIntensity_map_measurable measurableSet_Ioc)]
  have hl (x : ℝ) : a<NNReal.sqrt (Real.toNNReal x) ↔ (a : ℝ)^2<x := by
    rw [←not_le,NNReal.sqrt_le_iff_le_sq,not_le,Real.lt_toNNReal_iff_coe_lt,
      NNReal.coe_pow]
  have he : (fun x : ℝ => NNReal.sqrt (Real.toNNReal x)) ⁻¹' Ioc a b ∩ Ici 0 =
      Ioc ((a : ℝ)^2) ((b : ℝ)^2) := by
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_Ioc,mem_Ici,hl,
      NNReal.sqrt_le_iff_le_sq,Real.toNNReal_le_iff_le_coe,NNReal.coe_pow]
    exact ⟨fun h => h.1,fun h => ⟨h,(sq_nonneg (a : ℝ)).trans h.1.le⟩⟩
  rw [he,Real.volume_Ioc]

lemma quadraticLengthIntensity_singleton (b : ℝ≥0) :
    quadraticLengthIntensity {b}=0 := by
  rw [quadraticLengthIntensity,Measure.map_apply quadraticLengthIntensity_map_measurable
    (measurableSet_singleton b),Measure.restrict_apply
      (quadraticLengthIntensity_map_measurable (measurableSet_singleton b))]
  have he : (fun x : ℝ => NNReal.sqrt (Real.toNNReal x)) ⁻¹' {b} ∩ Ici 0 =
      {((b : ℝ)^2)} := by
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_Ici,
      NNReal.sqrt_eq_iff_eq_sq]
    constructor
    · intro h
      have hh := congrArg (fun y : ℝ≥0 => (y : ℝ)) h.1
      simpa only [Real.coe_toNNReal _ h.2,NNReal.coe_pow] using hh
    · intro h
      subst x
      exact ⟨by apply Subtype.ext; simp [Real.coe_toNNReal _ (sq_nonneg (b : ℝ))],
        sq_nonneg _⟩
  rw [he,measure_singleton]

instance : NullSingletonClass quadraticLengthIntensity := ⟨quadraticLengthIntensity_singleton⟩

instance : IsLocallyFiniteMeasure quadraticLengthIntensity := by
  constructor
  intro x
  refine ⟨Iic (x+1),Iic_mem_nhds (by simp),?_⟩
  rw [quadraticLengthIntensity_Iic]
  exact ENNReal.ofReal_lt_top

end WP.RandomGeometry
