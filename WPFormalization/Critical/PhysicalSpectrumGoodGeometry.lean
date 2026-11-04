import WPFormalization.Critical.PhysicalSpectrumComparisonBadEvents
import WPFormalization.Critical.NonsimpleNonPantsCounts

/- The genuine geometric good event is proved from the actual three-term
majorant. It is not assumed measurable. Its complement is contained in the
Borel comparison bad event; raw nonpants predicates need no Borel assertion. -/
noncomputable section
set_option maxHeartbeats 500000
universe u v w z
namespace WP.Critical
open WP.External WP.RandomGeometry WP.External.PantsCluster
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H)
  (S : SingleCurvePieceClassics A) {g n : ℕ} (L : ℝ≥0)

def PhysicalSpectrumGeometryGood (X : G.Moduli g n (fun _ => 0)) : Prop :=
  (¬HasShortSeparatingNonPants T L X) ∧
  (¬HasIntersectingShortPants T (2*(L:ℝ)) X) ∧
  ∀(hg : Stable g n)(γ : H.Primitive g n X)(hns : ¬H.simple γ),
    H.length γ≤L → HasPantsTopology (S.piece g n hg X γ hns).piece.model

lemma physicalSpectrumGeometryGood_of_off_bad
    {Mns Mint : G.Moduli g n (fun _ => 0) → ℝ≥0∞}
    (hns : ∀X,nonsimpleNonPantsCount A S X L ≤ Mns X)
    (hint : ∀X,allShortIntersectingSimpleTupleCount T X 2 (2*(L:ℝ)) ≤ Mint X)
    (X : G.Moduli g n (fun _ => 0))
    (hoff : X∉physicalSpectrumComparisonBadSet T L Mns Mint) :
    PhysicalSpectrumGeometryGood A T S L X := by
  refine ⟨physicalSpectrumComparison_no_separating_nonpants T L X hoff,
    physicalSpectrumComparison_no_intersecting_pants T L hint X hoff,?_⟩
  intro hg γ hγ hlen
  by_contra hp
  have hb : 1 ≤ nonsimpleNonPantsCount A S X L :=
    one_le_nonsimpleNonPantsCount_of_bad A S X L ⟨γ,⟨hg,hγ,hp⟩,hlen⟩
  exact not_le_of_gt (physicalSpectrumComparison_majorants_lt_one T L X hoff).1
    (hb.trans (hns X))

lemma physicalSpectrumGeometryBad_subset_comparison
    {Mns Mint : G.Moduli g n (fun _ => 0) → ℝ≥0∞}
    (hns : ∀X,nonsimpleNonPantsCount A S X L ≤ Mns X)
    (hint : ∀X,allShortIntersectingSimpleTupleCount T X 2 (2*(L:ℝ)) ≤ Mint X) :
    {X | ¬PhysicalSpectrumGeometryGood A T S L X} ⊆
      physicalSpectrumComparisonBadSet T L Mns Mint := by
  intro X hX
  by_contra hoff
  exact hX (physicalSpectrumGeometryGood_of_off_bad A T S L hns hint X hoff)

lemma critical_physicalSpectrumGeometryBad_probability_tendsto_zero
    (MI : MirzakhaniIntegration G H T) (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (Mns Mint : (g : ℕ) → G.Moduli g (n g) (fun _ => 0) → ℝ≥0∞)
    (hns : ∀ᶠg in atTop,Measurable (Mns g))
    (hint : ∀ᶠg in atTop,Measurable (Mint g))
    (hnsdom : ∀ᶠg in atTop,∀X,nonsimpleNonPantsCount A S X L ≤ Mns g X)
    (hintdom : ∀ᶠg in atTop,∀X,
      allShortIntersectingSimpleTupleCount T X 2 (2*(L:ℝ)) ≤ Mint g X)
    (hnsmean : Tendsto (fun g => ∫⁻X,Mns g X ∂wpProbability G g (n g)) atTop (𝓝 0))
    (hintmean : Tendsto (fun g => ∫⁻X,Mint g X ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    Tendsto (fun g => wpProbability G g (n g)
      {X | ¬PhysicalSpectrumGeometryGood A T S L X}) atTop (𝓝 0) := by
  have hh := critical_physicalSpectrumComparisonBadSet_probability_tendsto_zero
    T L MI n c hc hn Mns Mint hns hint hnsmean hintmean
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall (fun _ => bot_le)) ?_
  filter_upwards [hnsdom,hintdom] with g hg hi
  exact measure_mono (physicalSpectrumGeometryBad_subset_comparison A T S L hg hi)

end WP.Critical
