import WPFormalization.Critical.MixedFactorialMoments
import WPFormalization.Critical.MixedIntersectingDomination
import WPFormalization.Probability.TwoColorPointMeasuresLaws
import WPFormalization.Probability.TwoColorPointMeasuresPrefix
import WPFormalization.RandomGeometry.CurveWindowPointCounts
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry WP.Probability MeasureTheory Filter Set
open scoped Classical ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)

lemma finite_windows_common_bound {ι : Type*} [Fintype ι]
    (B : ι→RelCompactBorelWindow ℝ≥0) : ∃L : ℝ≥0,∀i,(B i).carrier⊆Iic L := by
  have h (i : ι) : ∃L : ℝ≥0,(B i).carrier⊆Iic L := by
    obtain ⟨L,hL⟩ := (B i).compactClosure.bddAbove
    exact ⟨L,fun _ hx => hL (subset_closure hx)⟩
  choose b hb using h
  refine ⟨∑i,b i,fun i x hx => ?_⟩
  change x≤∑i,b i
  exact le_trans (hb i hx) (Finset.single_le_sum (fun j _ => show 0≤b j from bot_le) (Finset.mem_univ i))

lemma shortIntersections_vanishing_all_of_ge_two (n : ℕ→ℕ)
    (hshort : ∀t : ℕ,2≤t→∀L : ℝ,0≤L→Tendsto
      (fun g => ∫⁻ X,allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    ∀t : ℕ,∀L : ℝ,0≤L→Tendsto
      (fun g => ∫⁻ X,allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  intro t L hL
  by_cases ht : 2≤t
  · exact hshort t ht L hL
  · have ht1 : t≤1 := by omega
    simpa only [allShortIntersectingSimpleTupleCount_zero_of_le_one T _ t ht1 L,lintegral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

include MI RG in
lemma critical_colored_factorial_moments_of_short_intersections
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (hshort : ∀t : ℕ,∀L : ℝ,0≤L→Tendsto
      (fun g => ∫⁻ X,allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0))
    (d : ℕ) (color : Fin d→Bool) (B : Fin d→RelCompactBorelWindow ℝ≥0)
    (hB : Pairwise (fun i j => color i=color j → Disjoint (B i).carrier (B j).carrier)) :
    MixedFactorialMomentLimit (fun g => wpProbability G g (n g))
      (fun g X i => (coloredLengthPointMeasure T X (color i)).count ℝ≥0 (B i))
      (fun i => (if color i then criticalPantsLengthIntensity c (B i).carrier else
        nonseparatingLengthIntensity (B i).carrier).toNNReal) := by
  obtain ⟨L,hBL⟩ := finite_windows_common_bound B
  apply critical_colored_factorial_moments_of_intersecting T MI RG n c hc hn d color B L hBL
    (fun i j hij => hB hij)
  intro a
  exact mixedIntersectingWindowTupleCount_tendsto_of_allShort T n
    (pantsSlotsCount a color) (nonsepSlotsCount a color) _ L
    (fun j => nonnegativeIntensity_window_image_bound _ L (hBL _))
    (hshort _ L L.2)

include MI RG in
lemma critical_mixed_poisson_pair_of_short_intersections
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (hshort : ∀t : ℕ,2≤t→∀L : ℝ,0≤L→Tendsto
      (fun g => ∫⁻ X,allShortIntersectingSimpleTupleCount T X t L
        ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    ∃Q : ProbabilityMeasure (PointMeasure TwoColorSpace),
      IsPoissonPointProcessLaw TwoColorSpace (criticalTwoColorIntensity c) Q ∧
      LawConverges (fun g => wpProbability G g (n g))
        (fun g X => (nonseparatingLengthPointMeasure T X,
          planarLengthPointMeasure H X 1 (by norm_num) 2)) Q twoColorDecode := by
  apply twoColor_poisson_pair_limit_of_color_window_factorials
    (fun g => wpProbability G g (n g))
    (fun g X => nonseparatingLengthPointMeasure T X)
    (fun g X => planarLengthPointMeasure H X 1 (by norm_num) 2)
    (WP.Spectral.wpProbability_eventually_probability P G n
      ((surviving_critical_cusps_tendsto n c hc hn).eventually_ge_atTop 1))
    nonseparatingLengthIntensity (criticalPantsLengthIntensity c)
  · filter_upwards [] with g
    constructor
    · intro B hB
      exact (nonseparatingLengthPointMeasure_measurable_count T MI B).aemeasurable
    · intro B hB
      apply aemeasurable_nnrealRationalWindows_counts_of_prefix
        (wpProbability G g (n g)) _ ?_ B hB
      intro b
      simp_rw [planarLengthPointMeasure_prefix_count]
      exact (H.measurable_planarCount g (n g) 2 _).aemeasurable
  · intro d color B hBrat hB
    have hm := critical_colored_factorial_moments_of_short_intersections T MI RG n c hc hn
      (shortIntersections_vanishing_all_of_ge_two T n hshort) d color B hB
    have he : (fun (g : ℕ) (X : G.Moduli g (n g) (fun _ => 0)) (i : Fin d) => (coloredLengthPointMeasure T X (color i)).count ℝ≥0 (B i))=
        (fun (g : ℕ) (X : G.Moduli g (n g) (fun _ => 0)) (i : Fin d) => if color i then
          (planarLengthPointMeasure H X 1 (by norm_num) 2).count ℝ≥0 (B i) else
          (nonseparatingLengthPointMeasure T X).count ℝ≥0 (B i)) := by
      funext g X i
      cases h : color i <;> rfl
    rwa [he] at hm
end WP.Critical
