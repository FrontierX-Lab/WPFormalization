import WPFormalization.Critical.SeparatingNonPantsCover
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External CutGraphOrbits Finset MeasureTheory
open scoped Classical ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  {g n : ℕ} (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
include hg in
lemma separatingNonPantsCount_le_cutFamilies :
    separatingNonPantsCount T X L≤badCutFamilyCount T 1 L X+markedCutFamilyCount T 1 L X := by
  have hb : (∑' _ : {a : SeparatingNonPantsCurve T X L // separatingNonPantsCanonicalBad T hg X L a},(1 : ℝ≥0∞))≤
      ∑' _ : BadCutWindowIndex T (t:=1) L X,(1 : ℝ≥0∞) :=
    ENNReal.tsum_comp_le_tsum_of_injective (separatingNonPantsBadIndex_injective T hg X L)
      (fun _ => (1 : ℝ≥0∞))
  have hm : (∑' _ : {a : SeparatingNonPantsCurve T X L // ¬separatingNonPantsCanonicalBad T hg X L a},(1 : ℝ≥0∞))≤
      ∑' _ : MarkedCutWindowIndex T (t:=1) L X,(1 : ℝ≥0∞) :=
    ENNReal.tsum_comp_le_tsum_of_injective (separatingNonPantsMarkedIndex_injective T hg X L)
      (fun _ => (1 : ℝ≥0∞))
  change (∑' _ : SeparatingNonPantsCurve T X L,(1 : ℝ≥0∞))≤_
  have he := tsum_one_subtype_partition (separatingNonPantsCanonicalBad T hg X L)
  have hs := add_le_add hb hm
  have hbe := badCutWindowIndex_tsum_one_eq T (t:=1) L X
  have hme := markedCutWindowIndex_tsum_one_eq T (t:=1) L X
  rw [hbe,hme] at hs
  exact he.le.trans hs
end WP.Critical
