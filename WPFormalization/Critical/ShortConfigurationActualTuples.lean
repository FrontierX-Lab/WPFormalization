import WPFormalization.Critical.ShortConfigurationRecordingClusterNetworks
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortSupportingPieceGeometry WP.External.ShortSupportingConstructionGeometry
open WP.External.ShortFundamentalGroupGeometry WP.External.ShortRegularNeighborhoodGeometry
open scoped Classical
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  (A:AmbientRealization H) {T:MulticurveTopology.{u,v,w,z} G H}
  (AC:AmbientCurveCompatibility A T) {g n r:ℕ} (X:G.Moduli g n (fun _=>0))

abbrev actualAmbientTuple (γ:Fin r→H.Primitive g n X) :=
  fun i=>A.primitiveEquiv g n X (γ i)
lemma actualAmbientTuple_injective (γ:Fin r→H.Primitive g n X) (hi:Function.Injective γ) :
    Function.Injective (actualAmbientTuple A X γ) := (A.primitiveEquiv g n X).injective.comp hi
include AC in
lemma actualAmbientTuple_simple (γ:Fin r→H.Primitive g n X) (hs:∀i,H.simple (γ i)) :
    ∀i,SimpleTrace (A.model g n X) (actualAmbientTuple A X γ i) :=
  fun i=>(AC.simple_iff g n X (γ i)).mp (hs i)
lemma actualAmbientTuple_short (γ:Fin r→H.Primitive g n X) (L:ℝ) (hl:∀i,H.length (γ i)≤L) :
    ∀i,(A.model g n X).curves.length (actualAmbientTuple A X γ i)≤L := by
  intro i
  rw [A.length_eq]
  exact hl i

abbrev actualTupleNetwork (γ:Fin r→H.Primitive g n X) (hi:Function.Injective γ)
    (hs:∀i,H.simple (γ i)) (SC:SegmentClassics (A.model g n X))
    (L:ℝ) (hL:0<L) (hl:∀i,H.length (γ i)≤L) :=
  tupleEmbeddedNetwork (A.model g n X) SC (actualAmbientTuple A X γ)
    (actualAmbientTuple_injective A X γ hi) (actualAmbientTuple_simple A AC X γ hs)
    L hL (actualAmbientTuple_short A X γ L hl)

include AC in
lemma actual_intersecting_tuple_nonisolated (γ:Fin r→H.Primitive g n X)
    (hi:Function.Injective γ) (hnd:¬∀i j,i≠j→T.disjoint (γ i) (γ j)) :
    ∃i,i∉isolatedIndices (A.model g n X) (actualAmbientTuple A X γ) := by
  by_contra h
  have hh:∀i,i∈isolatedIndices (A.model g n X) (actualAmbientTuple A X γ):=by simpa using h
  apply hnd
  intro i j hij
  apply (AC.disjoint_iff g n X (γ i) (γ j) (hi.ne hij)).mpr
  exact (Finset.mem_filter.mp (hh i)).2 j hij.symm

end WP.Critical.ShortConfiguration
