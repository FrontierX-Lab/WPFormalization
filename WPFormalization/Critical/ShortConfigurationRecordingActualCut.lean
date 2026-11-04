import WPFormalization.Critical.ShortConfigurationRecordingEssentialBoundary
noncomputable section
set_option maxHeartbeats 0
universe x y z a b
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortRegularNeighborhoodGeometry WP.External.ShortLoopStraighteningGeometry
open scoped Classical ENNReal
variable {P:WP.PsiTheory} {G:WeilPeterssonGeometry.{x,y} P}
  {HC:HyperbolicCurveGeometry.{x,y,z} G}

lemma exists_actual_cut_of_geodesics
    (A:AmbientRealization HC) (T:MulticurveTopology.{x,y,z,a} G HC)
    (C:AmbientCurveCompatibility A T) {g n:ℕ} (X:G.Moduli g n (fun _=>0))
    (s:Finset (A.model g n X).curves.Primitive)
    (hs:∀γ∈s,SimpleTrace (A.model g n X) γ)
    (hd:∀γ∈s,∀δ∈s,γ≠δ→Disjoint ((A.model g n X).curves.trace γ)
      ((A.model g n X).curves.trace δ)) :
    ∃κ:Fin s.card→HC.Primitive g n X,∃o:T.Orbit g n s.card,
      T.orbitMem o X κ ∧ (∑e,HC.length (κ e))=(∑γ∈s,(A.model g n X).curves.length γ) ∧
      (∀δ,δ∈s↔∃e,A.primitiveEquiv g n X (κ e)=δ) := by
  let e:Fin s.card≃s:=s.equivFin.symm
  let κ:Fin s.card→HC.Primitive g n X:=fun i=>(A.primitiveEquiv g n X).symm (e i).val
  have hinj:Function.Injective κ := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact (A.primitiveEquiv g n X).symm.injective hij
  have hsimple:∀i,HC.simple (κ i) := by
    intro i
    apply (C.simple_iff g n X (κ i)).mpr
    simpa [κ] using hs (e i).val (e i).property
  have hdisjoint:∀i j,i≠j→T.disjoint (κ i) (κ j) := by
    intro i j hij
    apply (C.disjoint_iff g n X (κ i) (κ j) (hinj.ne hij)).mpr
    simp only [κ,Equiv.apply_symm_apply]
    apply hd (e i).val (e i).property (e j).val (e j).property
    intro he
    exact hij (e.injective (Subtype.ext he))
  obtain ⟨o,ho,hu⟩:=T.orbit_partition X κ hinj hsimple hdisjoint
  refine ⟨κ,o,ho,?_,?_⟩
  · calc
      _ =∑i:Fin s.card,(A.model g n X).curves.length (e i).val := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa [κ] using (A.length_eq g n X (κ i)).symm
      _ =∑γ:s,(A.model g n X).curves.length γ.val :=
        e.sum_comp (fun γ:s=>(A.model g n X).curves.length γ.val)
      _ =∑γ∈s,(A.model g n X).curves.length γ := Finset.sum_coe_sort s _
  · intro δ
    constructor
    · intro hδ
      obtain ⟨j,hj⟩:=e.surjective ⟨δ,hδ⟩
      exact ⟨j,by simpa [κ] using congrArg Subtype.val hj⟩
    · rintro ⟨j,rfl⟩
      simpa [κ] using (e j).property

lemma exists_actual_network_cut
    (A:AmbientRealization HC) (T:MulticurveTopology.{x,y,z,a} G HC)
    (C:AmbientCurveCompatibility A T) {g n:ℕ} (X:G.Moduli g n (fun _=>0))
    (N:EmbeddedNetwork.{x,b} (A.model g n X).surface.Point) (D:NeighborhoodData N)
    (F:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (H:LoopStraighteningClassics (A.model g n X) (C.complete_domain g n X)) :
    ∃k≤2*Nat.card N.Edge,∃κ:Fin k→HC.Primitive g n X,∃o:T.Orbit g n k,
      T.orbitMem o X κ ∧ (∑e,HC.length (κ e))≤2*∑e,(N.finish e-N.start e) ∧
      ∀γ:HC.Primitive g n X,HC.simple γ→
        (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆N.support→
        (∃e,κ e=γ) ∨ ∀e,Disjoint
          ((A.model g n X).curves.trace (A.primitiveEquiv g n X γ))
          ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e))) := by
  let B:=A.model g n X
  let s:=essentialGeodesics B N D F (C.complete_domain g n X) H
  obtain ⟨κ,o,ho,hlen,hcover⟩:=exists_actual_cut_of_geodesics A T C X s
    (fun δ hδ=>essentialGeodesics_simple B N D F (C.complete_domain g n X) H hδ)
    (fun γ hγ δ hδ hne=>essentialGeodesics_disjoint B N D F
      (C.complete_domain g n X) H hγ hδ hne)
  refine ⟨s.card,essentialGeodesics_card_le B N D F (C.complete_domain g n X) H,κ,o,ho,?_,?_⟩
  · exact hlen.le.trans (essentialGeodesics_length_le B N D F (C.complete_domain g n X) H)
  · intro γ hsimple htrace
    by_cases hedge:∃e,κ e=γ
    · exact Or.inl hedge
    · right
      intro e
      have hδ:A.primitiveEquiv g n X (κ e)∈s:=(hcover _).mpr ⟨e,rfl⟩
      have h:=essentialGeodesics_edge_or_disjoint B N D F (C.complete_domain g n X) H
        ((C.simple_iff g n X γ).mp hsimple) htrace hδ
      exact h.resolve_left (by
        intro he
        exact hedge ⟨e,((A.primitiveEquiv g n X).injective he).symm⟩)
end WP.Critical.ShortConfiguration
