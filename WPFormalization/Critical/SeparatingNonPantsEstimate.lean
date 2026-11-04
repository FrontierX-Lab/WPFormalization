import WPFormalization.Critical.SeparatingNonPantsCoverBound
import WPFormalization.Critical.MixedWindowMoments
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External MeasureTheory Filter
open scoped Classical ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  (MI : MirzakhaniIntegration G H T)

include MI in
lemma critical_separatingNonPantsCount_tendsto_zero
    (L : ℝ) (hL : 0≤L) (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g : ℕ => ∫⁻ X,separatingNonPantsCount T X L
      ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  have hb := critical_badCutFamilyCount_tendsto_zero T MI 1 (by omega) L hL n c hc hn
  have hm := critical_markedCutFamilyCount_tendsto_zero T MI 1 (by omega) L hL n c hc hn
  have hu := hb.add hm
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    calc
      _ ≤ ∫⁻ X,badCutFamilyCount T 1 L X+markedCutFamilyCount T 1 L X
          ∂wpProbability G g (n g) :=
        lintegral_mono (fun X => separatingNonPantsCount_le_cutFamilies T hg X L)
      _ = _ := lintegral_add_left (badCutFamilyCount_measurable T MI 1 L) _
end WP.Critical
