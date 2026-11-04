import WPFormalization.Critical.ActualPiecePrimitiveMeasure
import WPFormalization.Critical.PhysicalSpectrumPartition
import WPFormalization.Critical.NonseparatingPointCounts

/- INTERNAL DETERMINISTIC CONSUMER, NOT A PRODUCER OF APPENDIX G.
The unique actual component assignment below is an ordinary explicit premise.
The G3 support/cut geometry still has to prove it on a high-probability event.
All catalogs, cut pieces, lengths and canonical clusters here are genuine. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z zz
namespace WP.Critical.PantsCluster
open WP.External WP.RandomGeometry WP.External.PantsCluster
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortBorderedLoopGeometry MeasureTheory Set
open scoped ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (A : AmbientRealization H)
  (T : MulticurveTopology.{u,v,w,z} G H)
  {g n k : ℕ} {o : T.Orbit g n k} (X : G.Moduli g n (fun _ => 0))
  {κ : Fin k → H.Primitive g n X} {hκ : T.orbitMem o X κ}
  (C : CutComponentRealization A T o X κ hκ)
  {ι : Type zz} [Fintype ι] (pieces : ι → Fin (T.cut o).components)

def actualCutClusterAssignment : Option ι → H.Primitive g n X → Prop
  | none,γ => IsNonseparating T γ
  | some i,γ => actualPiecePrimitivePredicate A X (C.piece (pieces i)) γ

lemma actual_finite_cluster_spectrum_of_unique_partition
    (F : Family.{u,w}) (U : UniquenessClassics F)
    (hpants : ∀i,HasPantsTopology (C.piece (pieces i)).model)
    (hb : ∀i,(C.piece (pieces i)).model.boundaries=1)
    (BC : ∀i,PrimitiveBoundaryClassics (C.piece (pieces i)).model
      (C.piece (pieces i)).boundary)
    (j : ∀i,Fin (C.piece (pieces i)).model.boundaries) (L : ℝ≥0)
    (hpartition : ∀γ : H.Primitive g n X,H.length γ≤L →
      ∃!i : Option ι,actualCutClusterAssignment A T X C pieces i γ) :
    (physicalPrimitiveLengthPointMeasure H X).toMeasure.restrict (Iic L) =
      ((nonseparatingLengthPointMeasure T X).toMeasure +
        Measure.sum (fun i : ι => measure F
          ⟨(C.piece (pieces i)).model.curves.length
              ((C.piece (pieces i)).boundary.curve (j i)),
            ((C.piece (pieces i)).model.curves.representative
              ((C.piece (pieces i)).boundary.curve (j i))).period_pos⟩)).restrict (Iic L) := by
  apply Measure.ext
  intro B hB
  rw [Measure.restrict_apply hB,Measure.restrict_apply hB,Measure.add_apply,
    Measure.sum_apply _ (hB.inter measurableSet_Iic),tsum_fintype]
  rw [physicalPrimitiveLengthPointMeasure_window_eq_sum H X
    (actualCutClusterAssignment A T X C pieces) L (B∩Iic L)
    inter_subset_right hpartition (hB.inter measurableSet_Iic),Fintype.sum_option]
  change curveNNLengthMeasure H X 1 (IsNonseparating T) (B∩Iic L) +
    (∑i : ι,curveNNLengthMeasure H X 1
      (actualPiecePrimitivePredicate A X (C.piece (pieces i))) (B∩Iic L)) = _
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [actual_cut_pants_H_measure_eq_cluster A X C F U (pieces i)
    (hpants i) (hb i) (BC i) (j i)]

end WP.Critical.PantsCluster
