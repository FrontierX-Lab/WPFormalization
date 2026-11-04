import WPFormalization.Critical.DisjointMixedMoments
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory Filter
open scoped Classical ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)

include MI in
lemma badCutFamilyCount_measurable {g n : ℕ} (t : ℕ) (L : ℝ) :
    Measurable (badCutFamilyCount T t L (g:=g) (n:=n)) := by
  apply Finset.measurable_sum
  intro q hq
  by_cases hQ : 1≤q.val
  · simp only [ite_eq_left hQ]
    apply Finset.measurable_sum
    intro S hS
    exact badPartitionCount_measurable T MI S.val L
  · simp only [ite_eq_right hQ]
    exact measurable_const

lemma mixedWindowTupleCount_zero {g n : ℕ} (X : G.Moduli g n (fun _ => 0))
    (I : Fin (0+0) → Set ℝ) : mixedWindowTupleCount T X I=1 := by
  rw [mixedWindowTupleCount_split T X I,mixedDisjointWindowTupleCount_zero T X I]
  suffices mixedIntersectingWindowTupleCount T X I=0 by simp only [this,add_zero]
  apply ENNReal.tsum_eq_zero.mpr
  intro γ
  exact False.elim (γ.property (fun i => Fin.elim0 i))

include MI RG in
lemma critical_mixed_window_tendsto_of_intersecting (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (L : ℝ) (hL : 0≤L) (hIL : ∀i,I i⊆Set.Icc 0 L)
    (hinter : Tendsto (fun g => ∫⁻ X,mixedIntersectingWindowTupleCount T X I
      ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    Tendsto (fun g => ∫⁻ X,mixedWindowTupleCount T X I ∂wpProbability G g (n g)) atTop
      (𝓝 (ENNReal.ofReal ((∏j : Fin r,∫s in I (j.castAdd k),criticalIntensityDensity c s)*
        ∏i : Fin k,∫t in I (Fin.natAdd r i),tightIntensityDensity t))) := by
  by_cases htotal : 1≤r+k
  · have hs := survivingMixed_window_expectation_tendsto T MI n c hc hn r k I hI L hL hIL
    have hb := critical_badCutFamilyCount_tendsto_zero T MI (r+k) htotal L hL n c hc hn
    have hu := (hs.add hb).add hinter
    simp only [add_zero] at hu
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hs hu
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
      apply lintegral_mono
      intro X
      change _ ≤ mixedWindowTupleCount T X I
      rw [mixedWindowTupleCount_decomposition T RG hg X I]
      exact le_trans le_self_add le_self_add
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
      calc
        _ ≤ ∫⁻ X,(survivingMixedOrbitSum T (survivingMixedWindowTest I) X+
            badCutFamilyCount T (r+k) L X)+mixedIntersectingWindowTupleCount T X I
            ∂wpProbability G g (n g) := by
          apply lintegral_mono
          intro X
          change mixedWindowTupleCount T X I ≤ _
          rw [mixedWindowTupleCount_decomposition T RG hg X I]
          exact add_le_add_left (add_le_add_right
            (mixedBadDisjointWindowTupleCount_le_badCutFamilyCount T RG hg htotal X I L hIL) _) _
        _ = _ := by
          have hsm : Measurable (fun X : G.Moduli g (n g) (fun _ => 0) =>
              survivingMixedOrbitSum T (survivingMixedWindowTest I) X) :=
            survivingMixedOrbitSum_measurable T MI _ (survivingMixedWindowTest_measurable I hI)
          have hbm : Measurable (fun X : G.Moduli g (n g) (fun _ => 0) =>
              badCutFamilyCount T (r+k) L X) := badCutFamilyCount_measurable T MI (r+k) L
          calc
            _ = (∫⁻ X,survivingMixedOrbitSum T (survivingMixedWindowTest I) X+
                badCutFamilyCount T (r+k) L X ∂wpProbability G g (n g))+
                ∫⁻ X,mixedIntersectingWindowTupleCount T X I ∂wpProbability G g (n g) :=
              lintegral_add_left (hsm.add hbm) _
            _ = _ := congrArg (fun z => z+∫⁻ X,mixedIntersectingWindowTupleCount T X I
              ∂wpProbability G g (n g)) (lintegral_add_left hsm _)

  · have hr : r=0 := by omega
    have hk : k=0 := by omega
    subst r k
    have hd := critical_disjoint_mixed_window_tendsto T MI RG n c hc hn 0 0 I hI L hL hIL
    convert hd using 1
    funext g
    apply lintegral_congr
    intro X
    rw [mixedWindowTupleCount_zero T,mixedDisjointWindowTupleCount_zero T]
end WP.Critical
