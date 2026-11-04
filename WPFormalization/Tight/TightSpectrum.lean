import WPFormalization.Tight.SpectrumPoissonConvergence
import WPFormalization.Tight.SpectrumPrefixConnectedProbability
import WPFormalization.Tight.SpectrumPrefixConnectedMeasurability
/- Original Theorem 14.4, on the original WP moduli space with its complete
primitive unoriented tight spectrum and its full geometric Consequently. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter WP.Probability SpectrumTupleExtensions
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}

/- All primitive tight curves counted below B on the normalized scale form
one complete simple, pairwise disjoint tuple whose filled cut is connected. -/
def actualTightPrefixGood (Q : TightGeodesicGeometry G T H)
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) (g n : ℕ) (B : ℝ)
    (X : G.Moduli g n (fun _=>0)) : Prop :=
  let Y:=(tightCuspMeasurableEquiv G g n).symm X
  ¬BadConfiguration Q Y (B/tightScale ((n:ℝ)/g)) ∧
    FullPrefixConnected Q A Y (B/tightScale ((n:ℝ)/g))

lemma measurableSet_actual_tight_prefix_good
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A) (g n : ℕ) (hg : 2≤g)
    (BM : TightGeodesicBorelModel G T H Q g n hg) (B : ℝ) :
    MeasurableSet {X : G.Moduli g n (fun _=>0) | actualTightPrefixGood Q A g n B X} := by
  exact ((measurableSet_actual_bad_configuration BM _).compl.inter
    (measurableSet_full_prefix_connected A MI hg BM _)).preimage
      (tightCuspMeasurableEquiv G g n).symm.measurable

theorem actual_tight_prefix_good_probability_tendsto_one
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A) (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop) (B : ℝ) (hB : 0≤B) :
    Tendsto (fun j=>wpProbability G (gs j) (ns j)
      {X | actualTightPrefixGood Q A (gs j) (ns j) B X}) atTop (𝓝 1) := by
  have h:=full_prefix_simple_disjoint_connected_probability_tendsto_one T BZ Q A MI D BM gs ns hgs B hB
  apply h.congr'
  apply Eventually.of_forall
  intro j
  have mp:=TightConnected.connected_cusp_probability_measurePreserving G (gs j) (ns j)
  have he:=(tightCuspMeasurableEquiv G (gs j) (ns j)).map_apply
    (μ:=TightConnected.connectedCuspProbability G (gs j) (ns j))
    {X | actualTightPrefixGood Q A (gs j) (ns j) B X}
  rw [mp.map_eq] at he
  exact (by simpa only [actualTightPrefixGood,Set.preimage_setOf_eq,
    MeasurableEquiv.symm_apply_apply] using he.symm)

/- Original Theorem 14.4, including its full geometric Consequently clause.
The spectrum contains every primitive unoriented tight geodesic, including
nonsimple ones; no cusp-density bound or limit is assumed. -/
@[blueprint "thm:tight-spectrum"]
theorem tight_length_spectrum
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A) (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (n : ℕ→ℕ) :
    ∃QL : ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL ∧
      LawConverges (fun g=>wpProbability G g (n g))
        (fun g=>actualScaledTightPointMeasure Q g (n g)) QL (fun ξ=>ξ) ∧
      ∀B : ℝ,0≤B→Tendsto (fun g=>wpProbability G g (n g)
        {X | actualTightPrefixGood Q A g (n g) B X}) atTop (𝓝 1) := by
  obtain ⟨QL,hPPP,hLaw⟩:=tight_spectrum_poisson_limit T BZ Q A MI D BM n
  exact ⟨QL,hPPP,hLaw,fun B hB=>actual_tight_prefix_good_probability_tendsto_one
    T BZ Q A MI D BM (fun g=>g) n tendsto_id B hB⟩

end WP.Tight
