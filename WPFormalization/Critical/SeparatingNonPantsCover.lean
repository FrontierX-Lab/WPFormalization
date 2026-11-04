import WPFormalization.Critical.SeparatingNonPantsCounts
import WPFormalization.Critical.CutMarkedFamilyIndex
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External CutGraphOrbits Finset MeasureTheory
open scoped Classical ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  {g n : ℕ} (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (L : ℝ)

def actualBadCutWindowIndex {t : ℕ} (ht : 1≤t) (o : T.Orbit g n t)
    (hb : CutGraphData.baseStableCount (T.cut o)≠1 ∨ CutGraphData.twoCount (T.cut o)≠0)
    (γ : Fin t→H.Primitive g n X) (ho : T.orbitMem o X γ)
    (hlen : (fun i => H.length (γ i))∈cutLengthBox t L) : BadCutWindowIndex T (t:=t) L X := by
  let D := T.cut o
  have hconn : D.ConnectedWithin univ := T.cut_connected o
  have hQ := CutGraphData.components_le_twice_edges D ht hconn
  have hQpos := CutGraphData.components_pos_of_connected D hconn
  have hc := CutGraphData.canonicalPartition_counts_le D
  let q : {q : Fin (2*t+1) // 1≤q.val} := ⟨⟨D.components,by omega⟩,hQpos⟩
  let S : {S : CutSkeleton t q.val.val // S.Connected} :=
    ⟨CutGraphData.actualSkeleton D,CutGraphData.actualSkeleton_connected D hconn⟩
  let p : {p : Fin (q.val.val+1)×(Fin (q.val.val+1)×Fin (q.val.val+1)) //
      p.2.2.val≠1 ∨ p.2.1.val≠0} :=
    ⟨(⟨CutGraphData.oneCount D,by dsimp [q];omega⟩,
      ⟨CutGraphData.twoCount D,by dsimp [q];omega⟩,
      ⟨CutGraphData.baseStableCount D,by dsimp [q];omega⟩),hb⟩
  let oo : Orbits T S.val (g:=g) (n:=n) := ⟨o,⟨CutGraphData.actualSkeletonRealization D⟩⟩
  have hpart : CutDataHasPartition (T.cut oo.val) p.val.1.val p.val.2.1.val p.val.2.2.val :=
    CutGraphData.has_canonicalPartition D ht hconn
  let po : ↥(partitionOrbits T S.val p.val.1.val p.val.2.1.val p.val.2.2.val) :=
    ⟨oo,(mem_partitionOrbits T S.val _ _ _ oo).mpr hpart⟩
  exact ⟨⟨q,S,p,po⟩,⟨γ,ho,hlen⟩⟩

def actualMarkedCutWindowIndex {t : ℕ} (ht : 1≤t) (o : T.Orbit g n t)
    (hm : CutDataHasMarkedPartition (T.cut o) (CutGraphData.oneCount (T.cut o))
      (CutGraphData.twoCount (T.cut o)) (CutGraphData.baseStableCount (T.cut o)))
    (γ : Fin t→H.Primitive g n X) (ho : T.orbitMem o X γ)
    (hlen : (fun i => H.length (γ i))∈cutLengthBox t L) : MarkedCutWindowIndex T (t:=t) L X := by
  let D := T.cut o
  have hconn : D.ConnectedWithin univ := T.cut_connected o
  have hQ := CutGraphData.components_le_twice_edges D ht hconn
  have hQpos := CutGraphData.components_pos_of_connected D hconn
  have hc := CutGraphData.canonicalPartition_counts_le D
  let q : {q : Fin (2*t+1) // 1≤q.val} := ⟨⟨D.components,by omega⟩,hQpos⟩
  let S : {S : CutSkeleton t q.val.val // S.Connected} :=
    ⟨CutGraphData.actualSkeleton D,CutGraphData.actualSkeleton_connected D hconn⟩
  let p : Fin (q.val.val+1)×(Fin (q.val.val+1)×Fin (q.val.val+1)) :=
    (⟨CutGraphData.oneCount D,by dsimp [q];omega⟩,
      ⟨CutGraphData.twoCount D,by dsimp [q];omega⟩,
      ⟨CutGraphData.baseStableCount D,by dsimp [q];omega⟩)
  let oo : Orbits T S.val (g:=g) (n:=n) := ⟨o,⟨CutGraphData.actualSkeletonRealization D⟩⟩
  let po : ↥(markedPartitionOrbits T S.val p.1.val p.2.1.val p.2.2.val) :=
    ⟨oo,(mem_markedPartitionOrbits T S.val _ _ _ oo).mpr hm⟩
  exact ⟨⟨q,S,p,po⟩,⟨γ,ho,hlen⟩⟩

def separatingNonPantsCurveOrbit (a : SeparatingNonPantsCurve T X L) : SeparatingNonPantsOrbit T g n :=
  ⟨simpleSingletonOrbit T a.val a.property.1.1,
    (separatingNonPants_iff_orbit T hg _ X a.val (simpleSingletonOrbit_mem T a.val a.property.1.1)).mp a.property.1⟩

lemma separatingNonPantsOrbit_canonical_marked (o : SeparatingNonPantsOrbit T g n)
    (hb : ¬(CutGraphData.baseStableCount (T.cut o.val)≠1 ∨ CutGraphData.twoCount (T.cut o.val)≠0)) :
    CutDataHasMarkedPartition (T.cut o.val) (CutGraphData.oneCount (T.cut o.val))
      (CutGraphData.twoCount (T.cut o.val)) (CutGraphData.baseStableCount (T.cut o.val)) := by
  have hw : CutGraphData.baseStableCount (T.cut o.val)=1 := by omega
  have hv : CutGraphData.twoCount (T.cut o.val)=0 := by omega
  have hpart : CutDataHasPartition (T.cut o.val) (CutGraphData.oneCount (T.cut o.val)) 0 1 := by
    simpa only [hv,hw] using CutGraphData.has_canonicalPartition (T.cut o.val) (by omega) (T.cut_connected o.val)
  rw [hv,hw]
  exact oneEdge_singleRoot_nonPants_marked (T.cut o.val) (T.cut_connected o.val) (T.cut_stable o.val)
    o.property.1 hpart o.property.2

def separatingNonPantsBadIndex (a : SeparatingNonPantsCurve T X L)
    (hb : CutGraphData.baseStableCount (T.cut (separatingNonPantsCurveOrbit T hg X L a).val)≠1 ∨
      CutGraphData.twoCount (T.cut (separatingNonPantsCurveOrbit T hg X L a).val)≠0) :
    BadCutWindowIndex T (t:=1) L X :=
  actualBadCutWindowIndex T X L (by omega) (separatingNonPantsCurveOrbit T hg X L a).val hb
    (fun _ => a.val) (simpleSingletonOrbit_mem T a.val a.property.1.1)
    ⟨fun _ => (H.length_pos a.val).le,fun _ => a.property.2⟩

def separatingNonPantsMarkedIndex (a : SeparatingNonPantsCurve T X L)
    (hb : ¬(CutGraphData.baseStableCount (T.cut (separatingNonPantsCurveOrbit T hg X L a).val)≠1 ∨
      CutGraphData.twoCount (T.cut (separatingNonPantsCurveOrbit T hg X L a).val)≠0)) :
    MarkedCutWindowIndex T (t:=1) L X :=
  actualMarkedCutWindowIndex T X L (by omega) (separatingNonPantsCurveOrbit T hg X L a).val
    (separatingNonPantsOrbit_canonical_marked T (separatingNonPantsCurveOrbit T hg X L a) hb)
    (fun _ => a.val) (simpleSingletonOrbit_mem T a.val a.property.1.1)
    ⟨fun _ => (H.length_pos a.val).le,fun _ => a.property.2⟩

def separatingNonPantsCanonicalBad (a : SeparatingNonPantsCurve T X L) : Prop :=
  CutGraphData.baseStableCount (T.cut (separatingNonPantsCurveOrbit T hg X L a).val)≠1 ∨
    CutGraphData.twoCount (T.cut (separatingNonPantsCurveOrbit T hg X L a).val)≠0

lemma separatingNonPantsBadIndex_injective :
    Function.Injective (fun a : {a : SeparatingNonPantsCurve T X L // separatingNonPantsCanonicalBad T hg X L a} =>
      separatingNonPantsBadIndex T hg X L a.val a.property) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  have hγ := congrArg (fun j : BadCutWindowIndex T (t:=1) L X => j.2.val 0) hab
  change a.val.val=b.val.val at hγ
  exact hγ

lemma separatingNonPantsMarkedIndex_injective :
    Function.Injective (fun a : {a : SeparatingNonPantsCurve T X L // ¬separatingNonPantsCanonicalBad T hg X L a} =>
      separatingNonPantsMarkedIndex T hg X L a.val a.property) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  have hγ := congrArg (fun j : MarkedCutWindowIndex T (t:=1) L X => j.2.val 0) hab
  change a.val.val=b.val.val at hγ
  exact hγ

lemma tsum_one_subtype_partition {α : Type*} (p : α→Prop) :
    (∑' _ : α,(1 : ℝ≥0∞))=(∑' _ : {a // p a},(1 : ℝ≥0∞))+
      ∑' _ : {a // ¬p a},(1 : ℝ≥0∞) := by
  calc
    _ = ∑' _ : {a // p a} ⊕ {a // ¬p a},(1 : ℝ≥0∞) :=
      ((Equiv.sumCompl p).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
    _ = ∑' j : {a // p a} ⊕ {a // ¬p a},
        Sum.elim (fun _ => (1 : ℝ≥0∞)) (fun _ => (1 : ℝ≥0∞)) j := by
      apply tsum_congr
      intro j
      cases j <;> rfl
    _ = _ := ENNReal.summable.tsum_sum ENNReal.summable

end WP.Critical
