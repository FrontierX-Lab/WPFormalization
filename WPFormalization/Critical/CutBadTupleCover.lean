import WPFormalization.Critical.CutBadTupleCoverIndex

/-! Actual nonsurviving disjoint mixed tuples inject into the finite bad
skeleton/partition/orbit cover, retaining the complete ordered primitive tuple. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd
namespace WP.Critical
open WP.External CutGraphOrbits Finset
open scoped Classical ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (RG : MulticurveRestrictionGeometry G H T) {g n r k : ℕ}
    (hg : 1≤g) (htotal : 1≤r+k) (X : G.Moduli g n (fun _ => 0))
    (I : Fin (r+k) → Set ℝ) (L : ℝ) (hIL : ∀i,I i ⊆ Set.Icc 0 L)

/-- The chosen actual cut orbit, its actual named skeleton, and its canonical
vertex partition. The tuple itself is retained as the final fibre coordinate. -/
def mixedBadTupleCoverIndex
    (a : {γ : MixedWindowTuple T X I // TupleDisjoint T γ.val ∧ ¬IsSurvivingTuple T γ.val}) :
    BadCutWindowIndex T (t:=r+k) L X := by
  let γ := a.val.val
  let o := mixedDisjointOrbit T γ a.val.property.1 a.val.property.2.1 a.property.1
  let D := T.cut o
  have hconn : D.ConnectedWithin univ := T.cut_connected o
  have hQ := CutGraphData.components_le_twice_edges D htotal hconn
  have hQpos := CutGraphData.components_pos_of_connected D hconn
  have hc := CutGraphData.canonicalPartition_counts_le D
  let q : {q : Fin (2*(r+k)+1) // 1≤q.val} := ⟨⟨D.components,by omega⟩,hQpos⟩
  let S : {S : CutSkeleton (r+k) q.val.val // S.Connected} :=
    ⟨CutGraphData.actualSkeleton D,CutGraphData.actualSkeleton_connected D hconn⟩
  have hb : CutGraphData.baseStableCount D≠1 ∨ CutGraphData.twoCount D≠0 :=
    nonsurviving_canonicalPartition_bad T RG hg htotal γ a.val.property.1 a.val.property.2.1
      a.property.1 a.property.2
  let p : {p : Fin (q.val.val+1)×(Fin (q.val.val+1)×Fin (q.val.val+1)) //
      p.2.2.val≠1 ∨ p.2.1.val≠0} :=
    ⟨(⟨CutGraphData.oneCount D,by dsimp [q];omega⟩,
      ⟨CutGraphData.twoCount D,by dsimp [q];omega⟩,
      ⟨CutGraphData.baseStableCount D,by dsimp [q];omega⟩),hb⟩
  let oo : Orbits T S.val (g:=g) (n:=n) :=
    ⟨o,⟨CutGraphData.actualSkeletonRealization D⟩⟩
  have hpart : CutDataHasPartition (T.cut oo.val) p.val.1.val p.val.2.1.val p.val.2.2.val :=
    CutGraphData.has_canonicalPartition D htotal hconn
  let po : ↥(partitionOrbits T S.val p.val.1.val p.val.2.1.val p.val.2.2.val) :=
    ⟨oo,(mem_partitionOrbits T S.val _ _ _ oo).mpr hpart⟩
  refine ⟨⟨q,S,p,po⟩,⟨γ,mixedDisjointOrbit_mem T γ a.val.property.1 a.val.property.2.1 a.property.1,?_⟩⟩
  exact ⟨fun i => (hIL i (a.val.property.2.2 i)).1,
    fun i => (hIL i (a.val.property.2.2 i)).2⟩

lemma mixedBadTupleCoverIndex_injective :
    Function.Injective (mixedBadTupleCoverIndex T RG hg htotal X I L hIL) := by
  intro a b hab
  have hγ := congrArg (fun j : BadCutWindowIndex T (t:=r+k) L X => j.2.val) hab
  change a.val.val=b.val.val at hγ
  exact Subtype.ext (Subtype.ext hγ)

include RG hg htotal hIL in
/-- Pointwise cover by the actual finite connected-skeleton bad partition
family. This is a count of actual typed primitive tuples, not an abstract
classification assumption or a bound for a substitute combinatorial model. -/
theorem mixedBadDisjointWindowTupleCount_le_badCutFamilyCount :
    mixedBadDisjointWindowTupleCount T X I ≤ badCutFamilyCount T (r+k) L X := by
  rw [←badCutWindowIndex_tsum_one_eq T L X]
  exact ENNReal.tsum_comp_le_tsum_of_injective
    (mixedBadTupleCoverIndex_injective T RG hg htotal X I L hIL) (fun _ => (1 : ℝ≥0∞))

end WP.Critical
