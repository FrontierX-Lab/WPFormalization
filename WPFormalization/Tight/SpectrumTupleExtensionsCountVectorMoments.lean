import WPFormalization.Tight.SpectrumTupleExtensionsCountVectorCore
import WPFormalization.Tight.SpectrumTupleExtensionsZeroLowerMarkedMoments
import WPFormalization.Tight.SpectrumTupleExtensionsOffBadIntegral
/- Actual primitive tight mixed factorial moments after the locally bounded
bad event is removed. The window-dependent truncation is used for the finite
count vector only. No global substitute process is used or assumed. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter SpectrumTupleExtensions WP.Probability
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H)
theorem off_bad_window_count_mixed_factorial_limit
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A) (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    {d : ℕ} (W : Fin d→RelCompactBorelWindow ℝ≥0) (hd : DisjointWindows ℝ≥0 W)
    (B : ℝ≥0) (hB : 0<(B:ℝ)) (hW : ∀i,(W i).carrier⊆Iic B) :
    MixedFactorialMomentLimit (fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j))
      (fun j=>offBadWindowCountVector Q (gs j) (ns j) (B:ℝ) W)
      (windowRates ℝ≥0 nonseparatingLengthIntensity W) := by
  intro m
  by_cases hm : ∀i,m i=0
  · apply tendsto_const_nhds.congr'
    filter_upwards [connected_cusp_probability_eventually_probability (G:=G) gs ns hgs] with j hj
    haveI := hj
    simp only [hm,Nat.descFactorial_zero,Nat.cast_one,Finset.prod_const_one,pow_zero,lintegral_one,measure_univ]
  · let I : Fin (∑i,m i)→Set ℝ := flatNNRealWindows W m
    have hI : ∀i,MeasurableSet (I i) := fun i=>
      nonnegativeIntensity_window_image_measurable _ (W ((blockIndexEquiv m).symm i).1).measurableSet
    have hIB : ∀i,I i⊆Icc (0:ℝ) (B:ℝ) := fun i=>
      nonnegativeIntensity_window_image_bound _ B (hW ((blockIndexEquiv m).symm i).1)
    have hgood := scaled_good_set_count_expectation_tendsto T BZ Q A MI (∑i,m i) gs ns hgs I hI
      (B:ℝ) B.2 hIB
    have hbad : Tendsto (fun j=>∫⁻X,
        if BadConfiguration Q X ((B:ℝ)/tightScale ((ns j:ℝ)/(gs j))) then
          (scaledGoodSetCount Q (gs j) (∑i,m i) (ns j) I X : ℝ≥0∞) else 0
        ∂TightConnected.connectedCuspProbability G (gs j) (ns j)) atTop (𝓝 0) := by
      apply (marked_scaled_good_count_expectation_tendsto_zero T BZ Q A MI D (∑i,m i) gs ns hgs
        I (B:ℝ) hB hIB).congr'
      apply Eventually.of_forall
      intro j
      apply lintegral_congr
      intro X
      by_cases hb : BadConfiguration Q X ((B:ℝ)/tightScale ((ns j:ℝ)/(gs j))) <;>
        simp only [hb,ite_true,ite_false,Nat.cast_zero]
    have hA : ∀ᶠj in atTop,MeasurableSet {X : TightSurface G (gs j) 0 (ns j) (fun _=>0) (fun _=>0) |
        BadConfiguration Q X ((B:ℝ)/tightScale ((ns j:ℝ)/(gs j)))} := by
      filter_upwards [hgs.eventually_ge_atTop 2] with j hj
      exact measurableSet_actual_bad_configuration (BM (gs j) (ns j) hj) _
    have ht:=WP.Probability.lintegral_off_events_tendsto
      (fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j))
      (fun j=>{X |BadConfiguration Q X ((B:ℝ)/tightScale ((ns j:ℝ)/(gs j)))}) hA
      (fun j X=>(scaledGoodSetCount Q (gs j) (∑i,m i) (ns j) I X : ℝ≥0∞))
      (∏i,tightIntensity (I i)) hgood hbad
    dsimp only [I] at ht
    rw [flat_intensity_product] at ht
    apply ht.congr'
    apply Eventually.of_forall
    intro j
    apply lintegral_congr
    intro X
    have hp:=congrArg (fun q : ℕ=>(q:ℝ≥0∞))
      (off_bad_mixed_factorial_eq_scaled_good_count Q X W hd m hm B hW)
    rw [Nat.cast_prod] at hp
    by_cases hb : BadConfiguration Q X ((B:ℝ)/tightScale ((ns j:ℝ)/(gs j))) <;>
      simpa only [Set.mem_setOf_eq,hb,ite_true,ite_false,Nat.cast_zero] using hp.symm

end WP.Tight
