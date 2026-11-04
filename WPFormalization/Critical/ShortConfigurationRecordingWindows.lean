import WPFormalization.Critical.CutMarkedFamilyIndex
import WPFormalization.Critical.CutCanonicalPartition
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.ShortConfiguration
open WP.External CutGraphOrbits Finset
open scoped Classical
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G} (T:MulticurveTopology.{u,v,w,z} G H)
  {g n k:ℕ} (L:ℝ) (X:G.Moduli g n (fun _=>0))

abbrev ActualCutWindow := BadCutWindowIndex T (t:=k) L X ⊕ MarkedCutWindowIndex T (t:=k) L X

def actualCutWindowOrbit (a:ActualCutWindow T L X (k:=k)) : T.Orbit g n k :=
  a.elim (fun w=>w.1.2.2.2.val.val) (fun w=>w.1.2.2.2.val.val)
def actualCutWindowTuple (a:ActualCutWindow T L X (k:=k)) : Fin k→H.Primitive g n X :=
  a.elim (fun w=>w.2.val) (fun w=>w.2.val)
def actualCutWindowQ (a:ActualCutWindow T L X (k:=k)) : ℕ :=
  a.elim (fun w=>w.1.1.val.val) (fun w=>w.1.1.val.val)

lemma actualCutWindow_mem (a:ActualCutWindow T L X (k:=k)) :
    T.orbitMem (actualCutWindowOrbit T L X a) X (actualCutWindowTuple T L X a) := by
  cases a with
  | inl w=>exact w.2.property.1
  | inr w=>exact w.2.property.1

noncomputable def actualCutWindowVertices (a:ActualCutWindow T L X (k:=k)) :
    Fin (T.cut (actualCutWindowOrbit T L X a)).components ≃ Fin (actualCutWindowQ T L X a) := by
  cases a with
  | inl w=>exact (realization T w.1.2.1.val w.1.2.2.2.val).vertices
  | inr w=>exact (realization T w.1.2.1.val w.1.2.2.2.val).vertices

lemma exists_actualCutWindow (o:T.Orbit g n k) (κ:Fin k→H.Primitive g n X)
    (hκ:T.orbitMem o X κ) (hk:1 ≤ k)
    (hlen:(fun e=>H.length (κ e))∈cutLengthBox k L)
    (hclass:(CutGraphData.baseStableCount (T.cut o)≠1 ∨ CutGraphData.twoCount (T.cut o)≠0) ∨
      CutDataHasMarkedPartition (T.cut o) (CutGraphData.oneCount (T.cut o))
        (CutGraphData.twoCount (T.cut o)) (CutGraphData.baseStableCount (T.cut o))) :
    ∃a:ActualCutWindow T L X (k:=k),actualCutWindowOrbit T L X a=o ∧ actualCutWindowTuple T L X a=κ := by
  let D:=T.cut o
  have hconn:=T.cut_connected o
  have hQ:=CutGraphData.components_le_twice_edges D hk hconn
  have hQpos:=CutGraphData.components_pos_of_connected D hconn
  have hc:=CutGraphData.canonicalPartition_counts_le D
  let q:{q:Fin (2*k+1)//1 ≤ q.val}:=⟨⟨D.components,by omega⟩,hQpos⟩
  let S:{S:CutSkeleton k q.val.val//S.Connected}:=
    ⟨CutGraphData.actualSkeleton D,CutGraphData.actualSkeleton_connected D hconn⟩
  let oo:Orbits T S.val (g:=g) (n:=n):=⟨o,⟨CutGraphData.actualSkeletonRealization D⟩⟩
  let p:Fin (q.val.val+1)×(Fin (q.val.val+1)×Fin (q.val.val+1)):=
    (⟨CutGraphData.oneCount D,by dsimp [q];omega⟩,
     ⟨CutGraphData.twoCount D,by dsimp [q];omega⟩,
     ⟨CutGraphData.baseStableCount D,by dsimp [q];omega⟩)
  rcases hclass with hb|hm
  · let pp:{p:Fin (q.val.val+1)×(Fin (q.val.val+1)×Fin (q.val.val+1))//p.2.2.val≠1 ∨ p.2.1.val≠0}:=⟨p,hb⟩
    let po:↥(partitionOrbits T S.val p.1.val p.2.1.val p.2.2.val):=
      ⟨oo,(mem_partitionOrbits T S.val _ _ _ oo).mpr (CutGraphData.has_canonicalPartition D hk hconn)⟩
    exact ⟨Sum.inl ⟨⟨q,S,pp,po⟩,⟨κ,hκ,hlen⟩⟩,rfl,rfl⟩
  · let po:↥(markedPartitionOrbits T S.val p.1.val p.2.1.val p.2.2.val):=
      ⟨oo,(mem_markedPartitionOrbits T S.val _ _ _ oo).mpr hm⟩
    exact ⟨Sum.inr ⟨⟨q,S,p,po⟩,⟨κ,hκ,hlen⟩⟩,rfl,rfl⟩
end WP.Critical.ShortConfiguration
