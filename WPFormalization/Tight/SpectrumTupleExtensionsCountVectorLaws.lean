import WPFormalization.Tight.SpectrumTupleExtensionsCountVectorMoments
import WPFormalization.Tight.SpectrumTupleExtensionsBadProbability
import WPFormalization.Probability.LawConvergenceBadEvent
/- Genuine unmodified tight spectrum count-vector laws. Each fixed window
family uses its own bounded bad event; the locally proved vanishing bad-event
probability transfers the factorial-moment law back to the original counts. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter SpectrumTupleExtensions WP.Probability
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H)
lemma measurable_scaled_tight_window_count_vector (g n : ℕ) (hg : 2≤g)
    (BM : TightGeodesicBorelModel G T H Q g n hg) {d : ℕ}
    (W : Fin d→RelCompactBorelWindow ℝ≥0) :
    Measurable (fun X=>windowCountVector ℝ≥0 W (scaledTightPointMeasure Q g n X)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_tightLengthPointMeasure_window_count Q BM _
    (TightConnected.tightScale_pos _ (by positivity)) (W i)

theorem actual_tight_window_count_law (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A) (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (gs ns : ℕ→ℕ) (hgs : Tendsto gs atTop atTop)
    {d : ℕ} (W : Fin d→RelCompactBorelWindow ℝ≥0) (hd : DisjointWindows ℝ≥0 W)
    (B : ℝ≥0) (hB : 0<(B:ℝ)) (hW : ∀i,(W i).carrier⊆Iic B) :
    LawConverges (fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j))
      (fun j X=>windowCountVector ℝ≥0 W (scaledTightPointMeasure Q (gs j) (ns j) X))
      (productPoissonMeasure (windowRates ℝ≥0 nonseparatingLengthIntensity W)) (fun z=>z) := by
  let μ :=fun j=>TightConnected.connectedCuspProbability G (gs j) (ns j)
  let Ξ :=fun j X=>windowCountVector ℝ≥0 W (scaledTightPointMeasure Q (gs j) (ns j) X)
  let Y :=fun j=>offBadWindowCountVector Q (gs j) (ns j) (B:ℝ) W
  have hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j) :=
    connected_cusp_probability_eventually_probability gs ns hgs
  have hX : ∀ᶠj in atTop,AEMeasurable (Ξ j) (μ j) := by
    filter_upwards [hgs.eventually_ge_atTop 2] with j hj
    exact (measurable_scaled_tight_window_count_vector Q (gs j) (ns j) hj (BM _ _ hj) W).aemeasurable
  have hY : ∀ᶠj in atTop,AEMeasurable (Y j) (μ j) := by
    filter_upwards [hgs.eventually_ge_atTop 2] with j hj
    exact (measurable_offBadWindowCountVector Q (gs j) (ns j) hj (BM _ _ hj) (B:ℝ) W).aemeasurable
  let E :=fun j=>{X : TightSurface G (gs j) 0 (ns j) (fun _=>0) (fun _=>0) |
    BadConfiguration Q X ((B:ℝ)/tightScale ((ns j:ℝ)/(gs j)))}
  have hE : ∀ᶠj in atTop,MeasurableSet (E j) := by
    filter_upwards [hgs.eventually_ge_atTop 2] with j hj
    exact measurableSet_actual_bad_configuration (BM _ _ hj) _
  have hXY : ∀ᶠj in atTop,∀X,X∉E j→Ξ j X=Y j X := by
    apply Eventually.of_forall
    intro j X hX
    funext i
    simp only [Y,offBadWindowCountVector,show ¬BadConfiguration Q X
      ((B:ℝ)/tightScale ((ns j:ℝ)/(gs j))) from hX,ite_false,Ξ,windowCountVector]
  have hbad : Tendsto (fun j=>(μ j).real (E j)) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def,Measure.real,μ,E] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (bad_configuration_measure_tendsto_zero T BZ Q A MI D BM gs ns hgs (B:ℝ) hB)
  have hmom := off_bad_window_count_mixed_factorial_limit T BZ Q A MI D BM gs ns hgs W hd B hB hW
  have hLaw := WP.External.factorial_moments_poisson_nonneg μ Y hprob hY
    (windowRates ℝ≥0 nonseparatingLengthIntensity W) hmom
  exact lawConverges_of_eq_off_bad_events μ Ξ Y _ (fun z=>z) hprob hX hY E hE hXY hbad hLaw

lemma finite_windows_common_positive_bound {d : ℕ}
    (W : Fin d→RelCompactBorelWindow ℝ≥0) :
    ∃B : ℝ≥0,0<(B:ℝ) ∧ ∀i,(W i).carrier⊆Iic B := by
  choose b hb using fun i=>(W i).compactClosure.bddAbove
  let B : ℝ≥0 := 1+∑i : Fin d,b i
  have hB : 0<(B:ℝ) := by dsimp [B];positivity
  refine ⟨B,hB,?_⟩
  intro i x hx
  have hxi : x≤b i := hb i (subset_closure hx)
  have hi : b i≤∑j : Fin d,b j := Finset.single_le_sum (fun j _=>zero_le) (Finset.mem_univ i)
  exact hxi.trans (hi.trans (by dsimp [B];exact le_add_of_nonneg_left (by norm_num : (0:ℝ≥0)≤1)))

end WP.Tight
