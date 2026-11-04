import VersoBlueprint.Attribute
import WPFormalization.Critical.ShortConfigurationRecordingActualCut
noncomputable section
set_option maxHeartbeats 0
universe x y z a
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortRegularNeighborhoodGeometry WP.External.ShortLoopStraighteningGeometry
open scoped Classical

@[blueprint "ext:short-filling"]
lemma exists_actual_short_simple_tuple_cut {P:WP.PsiTheory}
    {G:WeilPeterssonGeometry.{x,y} P} {HC:HyperbolicCurveGeometry.{x,y,z} G}
    (A:AmbientRealization HC) (T:MulticurveTopology.{x,y,z,a} G HC)
    (C:AmbientCurveCompatibility A T) {g n:ℕ} (X:G.Moduli g n (fun _=>0))
    (S:SegmentClassics (A.model g n X))
    (RN:RegularNeighborhoodClassics.{x,z,0} (A.model g n X) (C.complete_domain g n X))
    (F:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (H:LoopStraighteningClassics (A.model g n X) (C.complete_domain g n X))
    {r:ℕ} (γ:Fin r→HC.Primitive g n X) (hinj:Function.Injective γ)
    (hsimple:∀i,HC.simple (γ i)) (L:ℝ) (hL:0<L) (hlength:∀i,HC.length (γ i)≤L) :
    ∃k≤2*(r*(r*r*(Nat.floor (L/segmentScale L)+1)^2+1)),
      ∃κ:Fin k→HC.Primitive g n X,∃o:T.Orbit g n k,
      T.orbitMem o X κ ∧ (∑e,HC.length (κ e))≤2*r*L ∧
      ∀i,(∃e,κ e=γ i) ∨ ∀e,Disjoint
        ((A.model g n X).curves.trace (A.primitiveEquiv g n X (γ i)))
        ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e))) := by
  let B:=A.model g n X
  let β:Fin r→B.curves.Primitive:=fun i=>A.primitiveEquiv g n X (γ i)
  have hβinj:Function.Injective β := (A.primitiveEquiv g n X).injective.comp hinj
  have hβsimple:∀i,SimpleTrace B (β i):=fun i=>(C.simple_iff g n X (γ i)).mp (hsimple i)
  have hβlength:∀i,B.curves.length (β i)≤L:=fun i=>(A.length_eq g n X (γ i)).trans_le (hlength i)
  let N:=tupleEmbeddedNetwork B S β hβinj hβsimple L hL hβlength
  let D:=RN.realize N
  obtain ⟨k,hk,κ,o,ho,hlen,havoid⟩:=exists_actual_network_cut A T C X N D F H
  refine ⟨k,hk.trans (Nat.mul_le_mul_left 2
    (tupleEmbeddedNetwork_edges_bound B S β hβinj hβsimple L hL hβlength)),κ,o,ho,?_,?_⟩
  · apply hlen.trans
    have he:(∑e:N.Edge,(N.finish e-N.start e))=∑i,B.curves.length (β i):=
      tupleEmbeddedNetwork_total_length B S β hβinj hβsimple L hL hβlength
    rw [he]
    calc
      _ ≤2*∑_i:Fin r,L:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum
        (fun i hi=>hβlength i)) (by norm_num)
      _ =_:=by simp [mul_assoc]
  · intro i
    apply havoid (γ i) (hsimple i)
    rw [tupleEmbeddedNetwork_support B S β hβinj hβsimple L hL hβlength]
    exact Set.subset_iUnion (fun j=>B.curves.trace (β j)) i
end WP.Critical.ShortConfiguration
