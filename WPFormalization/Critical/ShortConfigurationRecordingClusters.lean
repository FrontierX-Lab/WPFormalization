import WPFormalization.Topology.FiniteIntersectionClusters
import WPFormalization.Critical.ShortConfigurationRecordingIsolatedEdges
import WPFormalization.Critical.ShortConfigurationRecordingCutFibers
import WPFormalization.External.ShortSupportingPieceGeometry
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortSupportingPieceGeometry
open WP.FiniteIntersectionClusters
open scoped Classical
variable (B:BorderedGeometry.{u,v}) {r:ℕ} (γ:Fin r→B.curves.Primitive)

def traceFamily : Fin r→Set B.surface.Point := fun i=>B.curves.trace (γ i)
abbrev CurveCluster := Cluster (traceFamily B γ)

def clusterPrimitives (c:CurveCluster B γ) : Finset B.curves.Primitive :=
  (members (traceFamily B γ) c).image γ

lemma clusterPrimitives_nonempty (c:CurveCluster B γ) : (clusterPrimitives B γ c).Nonempty:=
  (members_nonempty (traceFamily B γ) c).image γ

lemma clusterPrimitives_carrier (c:CurveCluster B γ) :
    WP.External.ShortSupportingPieceGeometry.carrier B (clusterPrimitives B γ c)=
      WP.FiniteIntersectionClusters.carrier (traceFamily B γ) c := by
  ext p
  simp only [WP.External.ShortSupportingPieceGeometry.carrier,
    WP.FiniteIntersectionClusters.carrier,Set.mem_iUnion,clusterPrimitives,Finset.mem_image]
  constructor
  · rintro ⟨δ,⟨i,hi,rfl⟩,hp⟩
    exact ⟨i,hi,hp⟩
  · rintro ⟨i,hi,hp⟩
    exact ⟨γ i,⟨i,hi,rfl⟩,hp⟩

lemma clusterPrimitives_preconnected (c:CurveCluster B γ) :
    IsPreconnected (WP.External.ShortSupportingPieceGeometry.carrier B (clusterPrimitives B γ c)) := by
  rw [clusterPrimitives_carrier]
  exact carrier_isPreconnected (traceFamily B γ) (fun i=>primitive_trace_preconnected B (γ i)) c

lemma clusterPrimitives_card (hinj:Function.Injective γ) (c:CurveCluster B γ) :
    (clusterPrimitives B γ c).card=(members (traceFamily B γ) c).card :=
  Finset.card_image_of_injective _ hinj

lemma clusterPrimitives_card_le (c:CurveCluster B γ) : (clusterPrimitives B γ c).card ≤ r:=
  Finset.card_image_le.trans ((Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp))

def ActiveCurveCluster := {c:CurveCluster B γ // 2 ≤ (members (traceFamily B γ) c).card}
instance : Fintype (ActiveCurveCluster B γ) := inferInstanceAs (Fintype {c:CurveCluster B γ // _})

lemma ActiveCurveCluster.card_le : Fintype.card (ActiveCurveCluster B γ) ≤ r := by
  calc
    _ ≤ Fintype.card (CurveCluster B γ):=Fintype.card_subtype_le _
    _ = Nat.card (CurveCluster B γ):=Nat.card_eq_fintype_card.symm
    _ ≤ Nat.card (Fin r):=Nat.card_le_card_of_surjective _ (cluster_surjective (traceFamily B γ))
    _ = r:=by simp

lemma active_cluster_member_not_isolated (c:ActiveCurveCluster B γ)
    (i:Fin r) (hi:i∈members (traceFamily B γ) c.val) : i∉isolatedIndices B γ := by
  intro hiso
  have hp:∀j,j≠i→Disjoint ((traceFamily B γ) i) ((traceFamily B γ) j):=
    (Finset.mem_filter.mp hiso).2
  have he:= (members_cluster_eq_singleton_iff (traceFamily B γ) i).mpr hp
  rw [(mem_members (traceFamily B γ) _ _).mp hi] at he
  have hh:=c.property
  rw [he] at hh
  simp at hh

lemma nonisolated_cluster_active (i:Fin r) (hi:i∉isolatedIndices B γ) :
    2 ≤ (members (traceFamily B γ) (cluster (traceFamily B γ) i)).card := by
  have hn:0<(members (traceFamily B γ) (cluster (traceFamily B γ) i)).card:=
    (members_nonempty _ _).card_pos
  by_contra h
  have hec:(members (traceFamily B γ) (cluster (traceFamily B γ) i)).card=1:=by omega
  obtain ⟨j,hj⟩:=Finset.card_eq_one.mp hec
  have hmi:i∈members (traceFamily B γ) (cluster (traceFamily B γ) i):=(mem_members _ _ _).mpr rfl
  have hij:i=j:=by simpa only [hj,Finset.mem_singleton] using hmi
  have he:members (traceFamily B γ) (cluster (traceFamily B γ) i)={i}:=by simpa [←hij] using hj
  have hp:∀j,j≠i→Disjoint ((traceFamily B γ) i) ((traceFamily B γ) j):=
    (members_cluster_eq_singleton_iff (traceFamily B γ) i).mp he
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)

def activeClusterOfNonisolated (i:Fin r) (hi:i∉isolatedIndices B γ) : ActiveCurveCluster B γ :=
  ⟨cluster (traceFamily B γ) i,nonisolated_cluster_active B γ i hi⟩

lemma mem_active_cluster_of_nonisolated (i:Fin r) (hi:i∉isolatedIndices B γ) :
    γ i∈clusterPrimitives B γ (activeClusterOfNonisolated B γ i hi).val :=
  Finset.mem_image.mpr ⟨i,(mem_members _ _ _).mpr rfl,rfl⟩

variable (hcomplete:B.surface.domain=univ) (SP:SupportingPieceClassics B hcomplete)

def activeClusterSupport (hinj:Function.Injective γ) (c:ActiveCurveCluster B γ) :
    SupportingPieceData B (clusterPrimitives B γ c.val) :=
  SP.support _ (clusterPrimitives_nonempty B γ c.val) (clusterPrimitives_preconnected B γ c.val)
    (Or.inl (by rw [clusterPrimitives_card B γ hinj];exact c.property))

end WP.Critical.ShortConfiguration
