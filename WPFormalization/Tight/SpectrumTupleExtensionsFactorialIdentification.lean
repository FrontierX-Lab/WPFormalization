import WPFormalization.Tight.SpectrumTupleExtensionsFactorials
import WPFormalization.Tight.SpectrumTupleExtensionsSetWindows
/- The full primitive tight spectrum has exactly the ordered-tuple mixed
falling-factorial count off the actual bounded bad event. All coordinates
are transported through the same H.Primitive, including nonsimple curves. -/
noncomputable section
universe u v w z
namespace WP.Tight
open External Set SpectrumTupleExtensions
open scoped NNReal ENNReal
lemma mixed_factorial_eq_good_set_count_of_not_bad {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {T : TightRegions G}
    {H : HyperbolicCurveGeometry.{u,v,w} G}
    (Q : TightGeodesicGeometry G T H) {g n d : ℕ}
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0))
    (s : ℝ) (hs : 0<s) (W : Fin d→WP.Probability.RelCompactBorelWindow ℝ≥0)
    (hd : WP.Probability.DisjointWindows ℝ≥0 W) (m : Fin d→ℕ)
    (B : ℝ≥0) (hW : ∀i,(W i).carrier⊆Iic B)
    (hnobad : ¬BadConfiguration Q X ((B:ℝ)/s)) :
    (∏i : Fin d,((tightLengthPointMeasure Q X s hs).count ℝ≥0 (W i)).descFactorial (m i)) =
      Nat.card {Γ : Fin (∑i,m i)→Curve Q X // GoodSetTuple Q X (flattenedPhysicalWindows s W m) Γ} := by
  have ha := actual_set_count_eq_good_set_count_of_not_bad Q X
    (flattenedPhysicalWindows s W m) ((B:ℝ)/s) (flattenedPhysicalWindows_bounded s hs W m B hW) hnobad
  exact (flat_tight_tuple_card_eq_mixed_factorial Q X s hs W hd m).symm.trans ha
end WP.Tight
