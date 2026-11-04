import WPFormalization.Critical.ShortConfigurationRecordingDartVariation
import WPFormalization.Critical.ShortConfigurationRecordingCyclePartition
import WPFormalization.Critical.ShortConfigurationBoundaryCycles
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set Finset
open scoped ENNReal
variable {X:Type u} [MetricSpace X] (N:EmbeddedNetwork.{u,v} X)
  (R:NetworkRotation N) (C:WP.External.FiniteCyclicIntervalGeometry.Classics)

lemma cycle_boundary_walk_variation_le (c:R.BoundaryCycle N) :
    (ClosedLoop.postcompose (cycleClosedLoop N R C c) (boundaryWalk N R)).length≤
      ∑d∈R.cycleDarts N c,ENNReal.ofReal (N.finish d.1-N.start d.1) := by
  let m:ℕ:=(R.cycleDarts N c).card
  have hm:0 < m:=cycleDarts_card_pos N R c
  have h:=(actual_boundary_walk_variation_le N R (cycleClosedLoop N R C c)
    m (cyclePartitionNode m hm) (cyclePartitionNode_monotone m hm)
    (cyclePartitionNode_zero m hm) (cyclePartitionNode_last m hm)
    (fun j=>(cycleDartEquiv N R c j).val) (cyclePartitionSegment m hm)
    (cyclePartitionSegment_monotone m hm) (cyclePartitionSegment_range m hm) (by
      intro j t
      have hp:cyclePartitionSegment m hm j t=cycleSegmentParameter N R c j t:=rfl
      rw [hp,cycleClosedLoop_segment]
      rfl))
  refine h.trans_eq ?_
  calc
    _ =∑d:{d // d∈R.cycleDarts N c},ENNReal.ofReal (N.finish d.val.1-N.start d.val.1) :=
      (cycleDartEquiv N R c).sum_comp (fun d=>ENNReal.ofReal (N.finish d.val.1-N.start d.val.1))
    _ =∑d∈R.cycleDarts N c,ENNReal.ofReal (N.finish d.1-N.start d.1) :=
      Finset.sum_coe_sort (R.cycleDarts N c) (fun d:NetworkDart N=>ENNReal.ofReal (N.finish d.1-N.start d.1))

lemma cycle_boundary_walk_variation_le_ofReal (c:R.BoundaryCycle N) :
    (ClosedLoop.postcompose (cycleClosedLoop N R C c) (boundaryWalk N R)).length≤
      ENNReal.ofReal (∑d∈R.cycleDarts N c,(N.finish d.1-N.start d.1)) := by
  have hs:(∑d∈R.cycleDarts N c,ENNReal.ofReal (N.finish d.1-N.start d.1))=
      ENNReal.ofReal (∑d∈R.cycleDarts N c,(N.finish d.1-N.start d.1)) :=
    (ENNReal.ofReal_sum_of_nonneg (fun d hd=>(sub_pos.mpr (N.interval_pos d.1)).le)).symm
  exact (cycle_boundary_walk_variation_le N R C c).trans_eq hs


lemma cycle_boundary_walk_total_variation_le :
    ∑c,(ClosedLoop.postcompose (cycleClosedLoop N R C c) (boundaryWalk N R)).length≤
      ENNReal.ofReal (2*∑e,(N.finish e-N.start e)) := by
  calc
    _ ≤∑c,ENNReal.ofReal (∑d∈R.cycleDarts N c,(N.finish d.1-N.start d.1)) :=
      Finset.sum_le_sum (fun c hc=>cycle_boundary_walk_variation_le_ofReal N R C c)
    _ =ENNReal.ofReal (∑c,∑d∈R.cycleDarts N c,(N.finish d.1-N.start d.1)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun c hc=>Finset.sum_nonneg
        (fun d hd=>(sub_pos.mpr (N.interval_pos d.1)).le))).symm
    _ =_:=congrArg ENNReal.ofReal (R.sum_boundary_weights N (fun e=>N.finish e-N.start e))
end WP.Critical.ShortConfiguration
