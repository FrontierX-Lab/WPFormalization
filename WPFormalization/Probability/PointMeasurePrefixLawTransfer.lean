import WPFormalization.External.PointMeasureLaplaceConvergence
import WPFormalization.Probability.LawConvergenceBadEvent

/- A local comparison of arbitrary genuine point-measure laws through
finite spatial prefixes. The bad event may depend on the prefix. Only
compact-test Laplace observables are compared there, so no full random
measure equality outside one global bad event is assumed. The generic
Laplace-to-vague classical Prop is explicit in the final theorem. -/
noncomputable section
universe u v
namespace WP.Probability
open MeasureTheory Filter Set
open scoped NNReal Topology CompactlySupported
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

lemma pointMeasure_integral_eq_of_prefix_restrict_eq
    (ξ η : PointMeasure ℝ≥0) (L : ℝ≥0) (f : C_c(ℝ≥0,ℝ))
    (hLf : tsupport f⊆Iic L)
    (he : ξ.toMeasure.restrict (Iic L)=η.toMeasure.restrict (Iic L)) :
    (∫x,f x ∂ξ.toMeasure)=∫x,f x ∂η.toMeasure := by
  have hz : ∀x,x∉Iic L→f x=0 := by
    intro x hx
    by_contra hn
    exact hx (hLf (subset_tsupport f hn))
  have hξ : (∫x in Iic L,f x ∂ξ.toMeasure)=∫x,f x ∂ξ.toMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  have hη : (∫x in Iic L,f x ∂η.toMeasure)=∫x,f x ∂η.toMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  rw [←hξ,he,hη]

lemma boundedContinuousFunction_integral_sub_le_observable_bad_event
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y : Ω→E)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (A : Set Ω) (_hA : MeasurableSet A) (f : BoundedContinuousFunction E ℝ)
    (hXY : ∀ω,ω∉A→f (X ω)=f (Y ω)) :
    ‖(∫ω,f (X ω) ∂μ)-(∫ω,f (Y ω) ∂μ)‖≤2*‖f‖*μ.real A := by
  have hiX:=boundedContinuousFunction_integrable_comp μ X hX f
  have hiY:=boundedContinuousFunction_integrable_comp μ Y hY f
  have he : (∫ω,f (X ω)-f (Y ω) ∂μ)=(∫ω in A,f (X ω)-f (Y ω) ∂μ) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro ω hω
    rw [hXY ω hω,sub_self]
  rw [←integral_sub hiX hiY,he]
  apply norm_setIntegral_le_of_norm_le_const (measure_lt_top μ A)
  intro ω _
  calc
    ‖f (X ω)-f (Y ω)‖≤‖f (X ω)‖+‖f (Y ω)‖:=norm_sub_le _ _
    _≤‖f‖+‖f‖:=add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
    _=2*‖f‖:=by ring

lemma lawConverges_of_prefix_eq_off_bad_events
    (C : WP.External.PointMeasureLaplaceConvergence.{u,v})
    {Ω : ℕ→Type u} [∀j,MeasurableSpace (Ω j)]
    {Ωlimit : Type v} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ)→Measure (Ω j))
    (X Y : (j : ℕ)→Ω j→PointMeasure ℝ≥0)
    (Q : Measure Ωlimit) [IsProbabilityMeasure Q]
    (Z : Ωlimit→PointMeasure ℝ≥0)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hY : ∀ᶠj in atTop,AEMeasurable (Y j) (μ j)) (hZ : AEMeasurable Z Q)
    (A : (L : ℝ≥0)→(j : ℕ)→Set (Ω j))
    (hA : ∀L,∀ᶠj in atTop,MeasurableSet (A L j))
    (hXY : ∀L,∀ᶠj in atTop,∀ω,ω∉A L j→
      (X j ω).toMeasure.restrict (Iic L)=(Y j ω).toMeasure.restrict (Iic L))
    (hbad : ∀L,Tendsto (fun j=>(μ j).real (A L j)) atTop (𝓝 0))
    (hLaw : LawConverges μ Y Q Z) : LawConverges μ X Q Z := by
  apply C Ω Ωlimit μ X Q Z hprob hX hZ
  intro f hf
  obtain ⟨L,hLf⟩:=(show IsCompact (tsupport f) from f.hasCompactSupport).bddAbove
  let t:=PoissonCluster.pointMeasureLaplaceTest f hf
  have hbound : ∀ᶠj in atTop,
      ‖(∫ω,t (X j ω) ∂μ j)-(∫ω,t (Y j ω) ∂μ j)‖≤2*‖t‖*(μ j).real (A L j) := by
    filter_upwards [hprob,hX,hY,hA L,hXY L] with j hp hx hy ha hxy
    haveI:=hp
    apply boundedContinuousFunction_integral_sub_le_observable_bad_event
      (μ j) (X j) (Y j) hx hy (A L j) ha t
    intro ω hω
    change Real.exp (-(∫x,f x ∂(X j ω).toMeasure))=
      Real.exp (-(∫x,f x ∂(Y j ω).toMeasure))
    rw [pointMeasure_integral_eq_of_prefix_restrict_eq (X j ω) (Y j ω) L f hLf (hxy ω hω)]
  have ht:=(hbad L).const_mul (2*‖t‖)
  simp only [mul_zero] at ht
  have hnorm:=squeeze_zero' (Eventually.of_forall (fun j=>norm_nonneg
    ((∫ω,t (X j ω) ∂μ j)-(∫ω,t (Y j ω) ∂μ j)))) hbound ht
  have hzero:=tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hs:=hzero.add (hLaw t)
  simpa only [zero_add,sub_add_cancel,t,PoissonCluster.pointMeasureLaplaceTest_apply] using hs

end WP.Probability
