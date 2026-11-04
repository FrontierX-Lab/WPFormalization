import WPFormalization.Critical.CutBadFamilyBounds
import WPFormalization.Critical.MixedGeometricTuples

/-! A finite skeleton/orbit cover with actual primitive-tuple fibres. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd
namespace WP.Critical
open WP.External CutGraphOrbits Finset MeasureTheory
open scoped Classical ENNReal

namespace CutGraphData
variable {n t : ℕ} (D : MulticurveCutData n t)
def actualSkeleton : CutSkeleton t D.components := ⟨D.edgeVertex⟩
lemma actualSkeleton_connected (hconn : D.ConnectedWithin univ) :
    (actualSkeleton D).Connected := by
  exact hconn

def actualSkeletonRealization : (actualSkeleton D).Realization D where
  vertices := Equiv.refl _
  flip := fun _ => false
  edge_eq _ _ := rfl

lemma canonicalPartition_counts_le :
    oneCount D ≤ D.components ∧ twoCount D ≤ D.components ∧
      baseStableCount D ≤ D.components := by
  have he := Fintype.card_congr (canonicalPartition D).vertices
  simp only [Fintype.card_fin,Fintype.card_sum] at he
  omega

lemma components_pos_of_connected (hconn : D.ConnectedWithin univ) : 1 ≤ D.components := by
  obtain ⟨i,_⟩ := hconn.1
  have := i.isLt
  omega
end CutGraphData

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    {g n t : ℕ}

abbrev BadCutOrbitIndex (g n t : ℕ) :=
  Σq : {q : Fin (2*t+1) // 1≤q.val},
    ΣS : {S : CutSkeleton t q.val.val // S.Connected},
      Σp : {p : Fin (q.val.val+1)×(Fin (q.val.val+1)×Fin (q.val.val+1)) //
        p.2.2.val≠1 ∨ p.2.1.val≠0},
        ↥(partitionOrbits T S.val (g:=g) (n:=n) p.val.1.val p.val.2.1.val p.val.2.2.val)

abbrev BadCutWindowIndex (L : ℝ) (X : G.Moduli g n (fun _ => 0)) :=
  Σj : BadCutOrbitIndex T g n t,
    {γ : Fin t → H.Primitive g n X // T.orbitMem j.2.2.2.val.val X γ ∧
      (fun i => H.length (γ i)) ∈ cutLengthBox t L}

lemma cutOrbitLengthBox_tsum_one {Q : ℕ} (S : CutSkeleton t Q)
    (o : Orbits T S (g:=g) (n:=n)) (L : ℝ) (X : G.Moduli g n (fun _ => 0)) :
    T.orbitSum o.val (cutLengthTest t L) X =
      ∑' _ : {γ : Fin t → H.Primitive g n X // T.orbitMem o.val X γ ∧
        (fun i => H.length (γ i))∈cutLengthBox t L},(1 : ℝ≥0∞) := by
  let p := fun γ : Fin t → H.Primitive g n X => T.orbitMem o.val X γ
  let q := fun γ : Fin t → H.Primitive g n X => (fun i => H.length (γ i))∈cutLengthBox t L
  have hs := tsum_subtype {γ : Subtype p | q γ.val} (fun _ => (1 : ℝ≥0∞))
  let e : {γ : Subtype p | q γ.val} ≃ {γ : Subtype p // q γ.val} := Equiv.refl _
  have he := (e.trans (Equiv.subtypeSubtypeEquivSubtypeInter p q)).tsum_eq (fun _ => (1 : ℝ≥0∞))
  calc
    _ = ∑' γ : Subtype p,if q γ.val then (1 : ℝ≥0∞) else 0 := rfl
    _ = ∑' _ : {γ : Subtype p | q γ.val},(1 : ℝ≥0∞) := by
      simpa only [Set.indicator,Set.mem_ofPred_eq] using hs.symm
    _ = _ := he

lemma badCutOrbitIndex_tsum_eq (L : ℝ) (X : G.Moduli g n (fun _ => 0)) :
    (∑' j : BadCutOrbitIndex T g n t,T.orbitSum j.2.2.2.val.val (cutLengthTest t L) X)=
      badCutFamilyCount T t L X := by
  simp_rw [ENNReal.tsum_sigma']
  let F : Fin (2*t+1) → ℝ≥0∞ := fun q =>
    ∑' S : {S : CutSkeleton t q.val // S.Connected},
      ∑' p : {p : Fin (q.val+1)×(Fin (q.val+1)×Fin (q.val+1)) //
        p.2.2.val≠1 ∨ p.2.1.val≠0},
        ∑' o : ↥(partitionOrbits T S.val (g:=g) (n:=n) p.val.1.val p.val.2.1.val p.val.2.2.val),
          T.orbitSum o.val.val (cutLengthTest t L) X
  change (∑' q : {q : Fin (2*t+1) // 1≤q.val},F q.val)=_
  have hqe : (∑' q : {q : Fin (2*t+1) // 1≤q.val},F q.val)=
      ∑'q : Fin (2*t+1),if 1≤q.val then F q else 0 := by
    have hs := _root_.tsum_subtype {q : Fin (2*t+1) | 1≤q.val} F
    convert hs using 1
    · rfl
    · apply tsum_congr
      intro q
      by_cases hq : 1≤q.val <;> simp [Set.indicator,hq]
  rw [hqe,tsum_fintype]
  unfold badCutFamilyCount
  apply sum_congr rfl
  intro q _
  by_cases hq : 1≤q.val
  · simp only [if_pos hq]
    dsimp only [F]
    rw [tsum_fintype]
    apply sum_congr rfl
    intro S _
    let Fp : Fin (q.val+1)×(Fin (q.val+1)×Fin (q.val+1)) → ℝ≥0∞ := fun p =>
      ∑' o : ↥(partitionOrbits T S.val (g:=g) (n:=n) p.1.val p.2.1.val p.2.2.val),
        T.orbitSum o.val.val (cutLengthTest t L) X
    change (∑' p : {p : Fin (q.val+1)×(Fin (q.val+1)×Fin (q.val+1)) //
      p.2.2.val≠1 ∨ p.2.1.val≠0},Fp p.val)=_
    have hpe : (∑' p : {p : Fin (q.val+1)×(Fin (q.val+1)×Fin (q.val+1)) //
        p.2.2.val≠1 ∨ p.2.1.val≠0},Fp p.val)=
        ∑'p,if p.2.2.val≠1 ∨ p.2.1.val≠0 then Fp p else 0 := by
      have hs := _root_.tsum_subtype
        {p : Fin (q.val+1)×(Fin (q.val+1)×Fin (q.val+1)) |
          p.2.2.val≠1 ∨ p.2.1.val≠0} Fp
      convert hs using 1
      · rfl
      · apply tsum_congr
        intro p
        by_cases hp : p.2.2.val≠1 ∨ p.2.1.val≠0 <;> simp only [Set.indicator,Set.mem_ofPred_eq]
        · rw [ite_eq_left hp,ite_eq_left hp]
        · rw [ite_eq_right hp,ite_eq_right hp]
    rw [hpe,tsum_fintype]
    unfold badPartitionCount
    apply sum_congr rfl
    intro p _
    by_cases hp : p.2.2.val≠1 ∨ p.2.1.val≠0
    · simp only [if_pos hp]
      exact Finset.tsum_subtype
        (partitionOrbits T S.val (g:=g) (n:=n) p.1.val p.2.1.val p.2.2.val)
        (fun o : Orbits T S.val (g:=g) (n:=n) => T.orbitSum o.val (cutLengthTest t L) X)
    · simp only [ite_eq_right hp]
  · simp only [ite_eq_right hq]

lemma badCutWindowIndex_tsum_one_eq (L : ℝ) (X : G.Moduli g n (fun _ => 0)) :
    (∑' _ : BadCutWindowIndex T (t:=t) L X,(1 : ℝ≥0∞))=badCutFamilyCount T t L X := by
  rw [ENNReal.tsum_sigma']
  simp_rw [←cutOrbitLengthBox_tsum_one T]
  exact badCutOrbitIndex_tsum_eq T L X

end WP.Critical
