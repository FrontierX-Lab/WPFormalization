import WPFormalization.Critical.MixedTupleDecomposition
import WPFormalization.Critical.MixedDisjointMeasurable
import WPFormalization.Critical.CutBadTupleCover
import WPFormalization.Spectral.VanishingGap
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory Filter
open scoped Classical ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)

lemma mixedDisjointWindowTupleCount_zero {g n : ℕ} (X : G.Moduli g n (fun _ => 0))
    (I : Fin (0+0) → Set ℝ) : mixedDisjointWindowTupleCount T X I=1 := by
  let γ : MixedWindowTuple T X I := ⟨Fin.elim0,(by intro i; exact Fin.elim0 i),
    ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩,fun i => Fin.elim0 i⟩
  let d : {γ : MixedWindowTuple T X I // TupleDisjoint T γ.val} :=
    ⟨γ,fun i => Fin.elim0 i⟩
  letI : Unique {γ : MixedWindowTuple T X I // TupleDisjoint T γ.val} :=
    ⟨⟨d⟩,fun a => by
      apply Subtype.ext
      apply Subtype.ext
      funext i
      exact Fin.elim0 i⟩
  unfold mixedDisjointWindowTupleCount
  rw [tsum_fintype]
  simp

include MI RG in
lemma critical_disjoint_mixed_window_tendsto (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (L : ℝ) (hL : 0≤L) (hIL : ∀i,I i⊆Set.Icc 0 L) :
    Tendsto (fun g => ∫⁻ X,mixedDisjointWindowTupleCount T X I ∂wpProbability G g (n g)) atTop
      (𝓝 (ENNReal.ofReal ((∏j : Fin r,∫s in I (j.castAdd k),criticalIntensityDensity c s)*
        ∏i : Fin k,∫t in I (Fin.natAdd r i),tightIntensityDensity t))) := by
  by_cases htotal : 1≤r+k
  · have hs := survivingMixed_window_expectation_tendsto T MI n c hc hn r k I hI L hL hIL
    have hb := critical_badCutFamilyCount_tendsto_zero T MI (r+k) htotal L hL n c hc hn
    have hu := hs.add hb
    simp only [add_zero] at hu
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hs hu
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
      apply lintegral_mono
      intro X
      change _ ≤ mixedDisjointWindowTupleCount T X I
      rw [mixedDisjointWindowTupleCount_split T X I,mixedSurvivingWindowTupleCount_eq T RG hg X I]
      exact le_self_add
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
      calc
        _ ≤ ∫⁻ X,survivingMixedOrbitSum T (survivingMixedWindowTest I) X+
            badCutFamilyCount T (r+k) L X ∂wpProbability G g (n g) := by
          apply lintegral_mono
          intro X
          change mixedDisjointWindowTupleCount T X I ≤ _
          rw [mixedDisjointWindowTupleCount_split T X I,mixedSurvivingWindowTupleCount_eq T RG hg X I]
          exact add_le_add_right (mixedBadDisjointWindowTupleCount_le_badCutFamilyCount T RG hg htotal X I L hIL) _
        _ = _ := lintegral_add_left (survivingMixedOrbitSum_measurable T MI _
          (survivingMixedWindowTest_measurable I hI)) _
  · have hr : r=0 := by omega
    have hk : k=0 := by omega
    subst r k
    have he : ENNReal.ofReal ((∏j : Fin 0,∫s in I (j.castAdd 0),criticalIntensityDensity c s)*
        ∏i : Fin 0,∫t in I (Fin.natAdd 0 i),tightIntensityDensity t)=1 := by simp
    rw [he]
    have hμ := WP.Spectral.wpProbability_eventually_probability P G n
      ((surviving_critical_cusps_tendsto n c hc hn).eventually_ge_atTop 1)
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 1)).congr'
    filter_upwards [hμ] with g hg
    letI : IsProbabilityMeasure (wpProbability G g (n g)) := hg
    simp only [mixedDisjointWindowTupleCount_zero T,lintegral_one,measure_univ]
end WP.Critical
