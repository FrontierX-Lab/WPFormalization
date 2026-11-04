import WPFormalization.Critical.MixedGeometricTuples
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry
open scoped Classical ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    {g n r k : ℕ}

lemma IsSurvivingTuple.disjoint {X : G.Moduli g n (fun _ => 0)}
    {γ : Fin (r+k) → H.Primitive g n X} (h : IsSurvivingTuple T γ) : TupleDisjoint T γ := by
  obtain ⟨o,ho⟩ := h
  exact T.orbit_disjoint o.val X γ ho

def survivingDisjointTupleEquiv (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    {γ : {γ : MixedWindowTuple T X I // TupleDisjoint T γ.val} // IsSurvivingTuple T γ.val.val} ≃
      {γ : MixedWindowTuple T X I // IsSurvivingTuple T γ.val} where
  toFun γ := ⟨γ.val.val,γ.property⟩
  invFun γ := ⟨⟨γ.val,IsSurvivingTuple.disjoint T γ.property⟩,γ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma mixedDisjointWindowTupleCount_split (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    mixedDisjointWindowTupleCount T X I=
      mixedSurvivingWindowTupleCount T X I+mixedBadDisjointWindowTupleCount T X I := by
  let A := {γ : MixedWindowTuple T X I // TupleDisjoint T γ.val}
  let p := fun γ : A => IsSurvivingTuple T γ.val.val
  have he := (Equiv.sumCompl p).tsum_eq (fun _ => (1 : ℝ≥0∞))
  rw [ENNReal.summable.tsum_sum ENNReal.summable] at he
  have hs := (survivingDisjointTupleEquiv T X I).tsum_eq (fun _ => (1 : ℝ≥0∞))
  have hb := (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun γ : MixedWindowTuple T X I => TupleDisjoint T γ.val)
    (fun γ : MixedWindowTuple T X I => ¬IsSurvivingTuple T γ.val)).tsum_eq (fun _ => (1 : ℝ≥0∞))
  exact he.symm.trans (congrArg₂ (·+·) hs hb)

lemma mixedWindowTupleCount_decomposition (RG : MulticurveRestrictionGeometry G H T) (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    mixedWindowTupleCount T X I=
      survivingMixedOrbitSum T (survivingMixedWindowTest I) X+
        mixedBadDisjointWindowTupleCount T X I+mixedIntersectingWindowTupleCount T X I := by
  rw [mixedWindowTupleCount_split T X I,mixedDisjointWindowTupleCount_split T X I,
    mixedSurvivingWindowTupleCount_eq T RG hg X I]
end WP.Critical
