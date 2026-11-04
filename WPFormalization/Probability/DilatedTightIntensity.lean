import WPFormalization.Probability.TwoColorPointMeasuresIntensities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.Algebra.GroupWithZero
/-! Exact change of density for the genuine nonseparating length intensity.
Positive inverse scaling is an ordinary measure pushforward. Its real-line
Lebesgue Jacobian cancels the scaled denominator, including the origin under
Lean's total division convention. All preservation properties are local; no
new external result is introduced. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Set
open scoped ENNReal NNReal Topology

def dilatedTightIntensity (a : ℝ) : Measure ℝ≥0 :=
  nonnegativeIntensity ((volume.restrict (Ici (0:ℝ))).withDensity
    (fun t => ENNReal.ofReal ((Real.cosh (a*t)-1)/t)))

lemma measurableEquiv_map_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e=(μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs,
    setLIntegral_map (f:=fun y => f (e.symm y)) hs
      (hf.comp e.symm.measurable) e.measurable]
  simp only [e.symm_apply_apply]

lemma nonnegativeIntensity_map_positive (ν : Measure ℝ) (b : ℝ) (hb : 0<b) :
    (nonnegativeIntensity ν).map (fun x : ℝ≥0 => Real.toNNReal b*x)=
      nonnegativeIntensity (ν.map (fun t : ℝ => b*t)) := by
  have hcoe : (Real.toNNReal b : ℝ)=b := Real.coe_toNNReal _ hb.le
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB,nonnegativeIntensity_apply,
    nonnegativeIntensity_apply,Measure.map_apply (by fun_prop)
      (nonnegativeIntensity_window_image_measurable B hB)]
  congr 1
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨Real.toNNReal b*x,hx,by simp only [NNReal.coe_mul,hcoe]⟩
  · rintro ⟨y,hy,he⟩
    have hy0 : 0≤b*t := by
      calc 0≤(y:ℝ) := y.property
           _ = b*t := he
    have ht : 0≤t := (mul_nonneg_iff_of_pos_left hb).mp hy0
    let x : ℝ≥0 := ⟨t,ht⟩
    refine ⟨x,?_,rfl⟩
    have heq : Real.toNNReal b*x=y := by
      apply Subtype.ext
      change (Real.toNNReal b : ℝ)*t=(y:ℝ)
      rw [hcoe]
      exact he.symm
    change Real.toNNReal b*x∈B
    rw [heq]
    exact hy

lemma tightIntensity_map_inverse (a : ℝ) (ha : 0<a) :
    tightIntensity.map (fun t : ℝ => a⁻¹*t)=
      (volume.restrict (Ici (0:ℝ))).withDensity
        (fun t => ENNReal.ofReal ((Real.cosh (a*t)-1)/t)) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ a⁻¹ (inv_ne_zero ha.ne')).toMeasurableEquiv
  have hf : Measurable (fun t => ENNReal.ofReal (tightIntensityDensity t)) := by
    unfold tightIntensityDensity
    fun_prop
  have hpre : (fun t : ℝ => a⁻¹*t) ⁻¹' Ici 0=Ici 0 := by
    ext t
    change 0≤a⁻¹*t ↔ 0≤t
    exact mul_nonneg_iff_of_pos_left (inv_pos.mpr ha)
  have hm : (volume.restrict (Ici (0:ℝ))).map (fun t => a⁻¹*t)=
      ENNReal.ofReal a • volume.restrict (Ici (0:ℝ)) := by
    rw [←hpre,←Measure.restrict_map (measurable_const_mul a⁻¹) measurableSet_Ici,
      Real.map_volume_mul_left (inv_ne_zero ha.ne'),Measure.restrict_smul]
    simp only [inv_inv,abs_of_pos ha,hpre]
  change ((volume.restrict (Ici (0:ℝ))).withDensity
    (fun t => ENNReal.ofReal (tightIntensityDensity t))).map e=_
  rw [measurableEquiv_map_withDensity e _ _ hf]
  change ((volume.restrict (Ici (0:ℝ))).map (fun t => a⁻¹*t)).withDensity
    (fun t => ENNReal.ofReal (tightIntensityDensity ((a⁻¹)⁻¹*t)))=_
  simp only [inv_inv]
  rw [hm,withDensity_smul_measure]
  rw [←withDensity_smul (μ:=volume.restrict (Ici (0:ℝ)))
    (f:=fun t => ENNReal.ofReal (tightIntensityDensity (a*t)))
    (ENNReal.ofReal a) (hf.comp (measurable_const_mul a))]
  congr 1
  funext t
  change ENNReal.ofReal a*ENNReal.ofReal (tightIntensityDensity (a*t))=_
  rw [←ENNReal.ofReal_mul ha.le]
  congr 1
  unfold tightIntensityDensity
  by_cases ht : t=0
  · simp [ht]
  · field_simp [ha.ne',ht]

lemma nonseparatingLengthIntensity_map_inverse (a : ℝ) (ha : 0<a) :
    nonseparatingLengthIntensity.map (fun x : ℝ≥0 => Real.toNNReal a⁻¹*x)=
      dilatedTightIntensity a := by
  rw [nonseparatingLengthIntensity,nonnegativeIntensity_map_positive _ a⁻¹ (inv_pos.mpr ha),
    tightIntensity_map_inverse a ha]
  rfl

lemma dilatedTightIntensity_locallyFinite (a : ℝ) (ha : 0<a) :
    IsLocallyFiniteMeasure (dilatedTightIntensity a) := by
  rw [←nonseparatingLengthIntensity_map_inverse a ha]
  have hc : Real.toNNReal a⁻¹≠0 := (Real.toNNReal_pos.mpr (inv_pos.mpr ha)).ne'
  let e : ℝ≥0 ≃ₜ ℝ≥0 := Homeomorph.mulLeft₀ (Real.toNNReal a⁻¹) hc
  change IsLocallyFiniteMeasure (nonseparatingLengthIntensity.map e)
  constructor
  intro x
  obtain ⟨U,hU,hfin⟩ := IsLocallyFiniteMeasure.finiteAtNhds
    (μ:=nonseparatingLengthIntensity) (e.symm x)
  refine ⟨e.symm ⁻¹' U,e.symm.continuous.continuousAt hU,?_⟩
  rw [e.measurableEmbedding.map_apply]
  have he : e ⁻¹' (e.symm ⁻¹' U)=U := by ext z;simp
  rw [he]
  exact hfin

lemma dilatedTightIntensity_regular (a : ℝ) (ha : 0<a) :
    Measure.Regular (dilatedTightIntensity a) := by
  let := dilatedTightIntensity_locallyFinite a ha
  infer_instance

lemma dilatedTightIntensity_nullSingleton (a : ℝ) (ha : 0<a) :
    NullSingletonClass (dilatedTightIntensity a) := by
  rw [←nonseparatingLengthIntensity_map_inverse a ha]
  have hc : Real.toNNReal a⁻¹≠0 := (Real.toNNReal_pos.mpr (inv_pos.mpr ha)).ne'
  let e : ℝ≥0 ≃ₜ ℝ≥0 := Homeomorph.mulLeft₀ (Real.toNNReal a⁻¹) hc
  change NullSingletonClass (nonseparatingLengthIntensity.map e)
  constructor
  intro x
  rw [e.measurableEmbedding.map_apply]
  have he : e ⁻¹' {x}={e.symm x} := by
    ext z
    change e z=x ↔ z=e.symm x
    constructor
    · intro hz
      simpa only [e.symm_apply_apply] using congrArg e.symm hz
    · intro hz
      rw [hz,e.apply_symm_apply]
  rw [he,measure_singleton]

lemma dilatedTightIntensity_one : dilatedTightIntensity 1=nonseparatingLengthIntensity := by
  have he := (nonseparatingLengthIntensity_map_inverse 1 (by norm_num)).symm
  simpa only [inv_one,Real.toNNReal_one,one_mul,Measure.map_id'] using he

end WP.Probability
