import WPFormalization.Tight.SpectrumTupleExtensionsPointProcess
import WPFormalization.Tight.ConnectedOrbitProbability
/- Appendix F.4 local actual-spectrum proof. The original normalized WP
measure and the complete primitive tight catalogue are retained; all limits
are proved from the previously formalized geometric moment producers. -/
noncomputable section
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H)

def scaledTightPointMeasure (g n : ℕ)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) : WP.Probability.PointMeasure ℝ≥0 :=
  tightLengthPointMeasure Q X (tightScale ((n:ℝ)/g))
    (TightConnected.tightScale_pos _ (by positivity))

def actualScaledTightPointMeasure (g n : ℕ) (X : G.Moduli g n (fun _=>0)) :
    WP.Probability.PointMeasure ℝ≥0 :=
  scaledTightPointMeasure Q g n ((tightCuspMeasurableEquiv G g n).symm X)

lemma aemeasurable_actualScaledTightPointMeasure (g n : ℕ) (hg : 2≤g)
    (BM : TightGeodesicBorelModel G T H Q g n hg) :
    AEMeasurable (actualScaledTightPointMeasure Q g n) (wpProbability G g n) := by
  apply WP.External.pointMeasure_nnreal_aemeasurable_of_prefix_counts
  intro b
  exact ((measurable_tightLengthPointMeasure_prefix_count Q BM
    (tightScale ((n:ℝ)/g)) (TightConnected.tightScale_pos _ (by positivity)) b).comp
      (tightCuspMeasurableEquiv G g n).symm.measurable).aemeasurable

lemma connected_cusp_probability_eventually_probability (gs ns : ℕ→ℕ)
    (hgs : Tendsto gs atTop atTop) :
    ∀ᶠj in atTop,IsProbabilityMeasure (TightConnected.connectedCuspProbability G (gs j) (ns j)) := by
  obtain ⟨N,hN⟩:=TightConnected.connected_cusp_volume_positive_eventually P G
  filter_upwards [hgs.eventually_ge_atTop (max N 2)] with j hj
  have hst : Stable (gs j) (ns j) := by unfold Stable;omega
  have hp := hN (gs j) (le_of_max_le_left hj) (ns j)
  have hmass : G.wpMeasure (gs j) (ns j) (fun _=>0) univ≠0 := by
    intro hm
    have : cuspVolume G (gs j) (ns j)=0 := by simp [cuspVolume,wpVolume,hm]
    linarith
  haveI := wpProbability_isProbabilityMeasure G (gs j) (ns j) hst hmass
  have mp:=TightConnected.connected_cusp_probability_measurePreserving G (gs j) (ns j)
  apply isProbabilityMeasure_iff.mpr
  have he := congrArg (fun μ=>μ univ) mp.map_eq
  rw [Measure.map_apply mp.measurable MeasurableSet.univ] at he
  simpa only [Set.preimage_univ,measure_univ] using he

lemma lawConverges_actualScaledTightPointMeasure_of_prefix
    (gs ns : ℕ→ℕ) (QL : ProbabilityMeasure (WP.Probability.PointMeasure ℝ≥0))
    (hLaw : WP.Probability.LawConverges
      (fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j))
      (fun j=>scaledTightPointMeasure Q (gs j) (ns j)) QL (fun ξ=>ξ)) :
    WP.Probability.LawConverges (fun j=>wpProbability G (gs j) (ns j))
      (fun j=>actualScaledTightPointMeasure Q (gs j) (ns j)) QL (fun ξ=>ξ) := by
  intro f
  have he (j : ℕ) : (∫X,f (actualScaledTightPointMeasure Q (gs j) (ns j) X)
      ∂wpProbability G (gs j) (ns j)) =
      ∫X,f (scaledTightPointMeasure Q (gs j) (ns j) X)
        ∂TightConnected.connectedCuspProbability G (gs j) (ns j) := by
    have mp:=TightConnected.connected_cusp_probability_measurePreserving G (gs j) (ns j)
    simpa only [actualScaledTightPointMeasure,MeasurableEquiv.symm_apply_apply] using
      (mp.integral_comp' (fun X=>f (actualScaledTightPointMeasure Q (gs j) (ns j) X))).symm
  simpa only [he] using hLaw f

end WP.Tight
