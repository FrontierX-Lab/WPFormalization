import WPFormalization.Critical.CutMarkedFamilyBounds
import WPFormalization.Critical.CutBadTupleCoverIndex
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd
namespace WP.Critical
open WP.External CutGraphOrbits Finset MeasureTheory
open scoped Classical ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    {g n t : ℕ}

abbrev MarkedCutOrbitIndex (g n t : ℕ) :=
  Σq : {q : Fin (2*t+1) // 1≤q.val},
    ΣS : {S : CutSkeleton t q.val.val // S.Connected},
      Σp : Fin (q.val.val+1)×(Fin (q.val.val+1)×Fin (q.val.val+1)),
        ↥(markedPartitionOrbits T S.val (g:=g) (n:=n) p.1.val p.2.1.val p.2.2.val)

abbrev MarkedCutWindowIndex (L : ℝ) (X : G.Moduli g n (fun _ => 0)) :=
  Σj : MarkedCutOrbitIndex T g n t,
    {γ : Fin t→H.Primitive g n X // T.orbitMem j.2.2.2.val.val X γ ∧
      (fun i => H.length (γ i))∈cutLengthBox t L}

lemma markedCutOrbitIndex_tsum_eq (L : ℝ) (X : G.Moduli g n (fun _ => 0)) :
    (∑' j : MarkedCutOrbitIndex T g n t,T.orbitSum j.2.2.2.val.val (cutLengthTest t L) X)=
      markedCutFamilyCount T t L X := by
  simp_rw [ENNReal.tsum_sigma']
  let F : Fin (2*t+1)→ℝ≥0∞ := fun q =>
    ∑'S : {S : CutSkeleton t q.val // S.Connected},
      ∑'p : Fin (q.val+1)×(Fin (q.val+1)×Fin (q.val+1)),
        ∑'o : ↥(markedPartitionOrbits T S.val (g:=g) (n:=n) p.1.val p.2.1.val p.2.2.val),
          T.orbitSum o.val.val (cutLengthTest t L) X
  change (∑'q : {q : Fin (2*t+1) // 1≤q.val},F q.val)=_
  have hqe : (∑'q : {q : Fin (2*t+1) // 1≤q.val},F q.val)=
      ∑'q : Fin (2*t+1),if 1≤q.val then F q else 0 := by
    have hs := _root_.tsum_subtype {q : Fin (2*t+1) | 1≤q.val} F
    convert hs using 1
    · rfl
    · apply tsum_congr
      intro q
      by_cases hq : 1≤q.val <;> simp [Set.indicator,hq]
  rw [hqe,tsum_fintype]
  unfold markedCutFamilyCount
  apply sum_congr rfl
  intro q hq
  by_cases hQ : 1≤q.val
  · simp only [ite_eq_left hQ]
    dsimp only [F]
    rw [tsum_fintype]
    apply sum_congr rfl
    intro S hS
    rw [tsum_fintype]
    unfold markedPartitionFamilyCount
    apply sum_congr rfl
    intro p hp
    exact Finset.tsum_subtype
      (markedPartitionOrbits T S.val (g:=g) (n:=n) p.1.val p.2.1.val p.2.2.val)
      (fun o : Orbits T S.val (g:=g) (n:=n) => T.orbitSum o.val (cutLengthTest t L) X)
  · simp only [ite_eq_right hQ]

lemma markedCutWindowIndex_tsum_one_eq (L : ℝ) (X : G.Moduli g n (fun _ => 0)) :
    (∑' _ : MarkedCutWindowIndex T (t:=t) L X,(1 : ℝ≥0∞))=markedCutFamilyCount T t L X := by
  rw [ENNReal.tsum_sigma']
  simp_rw [←cutOrbitLengthBox_tsum_one T]
  exact markedCutOrbitIndex_tsum_eq T L X
end WP.Critical
