import WPFormalization.Critical.ShortConfigurationRecordingIsolatedEdges
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortRegularNeighborhoodGeometry WP.External.ShortLoopStraighteningGeometry
variable {P:WP.PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
open scoped Classical

lemma exists_actual_augmented_tuple_cut
    (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
    (AC:AmbientCurveCompatibility A T) {g n r:ℕ} (X:G.Moduli g n (fun _=>0))
    (γ:Fin r→H.Primitive g n X) (hinj:Function.Injective γ)
    (hsimple:∀i,H.simple (γ i))
    (N:EmbeddedNetwork.{u,0} (A.model g n X).surface.Point)
    (htrace:∀i,(A.model g n X).curves.trace (A.primitiveEquiv g n X (γ i))⊆N.support)
    (D:NeighborhoodData N) (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X)) :
    ∃k ≤ 2*Nat.card N.Edge+r,∃κ:Fin k→H.Primitive g n X,∃o:T.Orbit g n k,
      ∃hκ:T.orbitMem o X κ,
      (∑e,H.length (κ e)) ≤ 2*(∑e,(N.finish e-N.start e))+(∑i,H.length (γ i)) ∧
      (∀i∈isolatedIndices (A.model g n X) (fun i=>A.primitiveEquiv g n X (γ i)),
        ∃e,κ e=γ i) ∧
      (∀i,i∉isolatedIndices (A.model g n X) (fun i=>A.primitiveEquiv g n X (γ i))→
        ∀e,Disjoint ((A.model g n X).curves.trace (A.primitiveEquiv g n X (γ i)))
          ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e)))) ∧
      (∀δ,δ∈augmentedGeodesics (A.model g n X) (fun i=>A.primitiveEquiv g n X (γ i))
        N D C (AC.complete_domain g n X) LS ↔∃e,A.primitiveEquiv g n X (κ e)=δ) := by
  let B:=A.model g n X
  let Γ:Fin r→B.curves.Primitive:=fun i=>A.primitiveEquiv g n X (γ i)
  have hΓ:Function.Injective Γ:=(A.primitiveEquiv g n X).injective.comp hinj
  have hs:∀i,SimpleTrace B (Γ i):=fun i=>(AC.simple_iff g n X (γ i)).mp (hsimple i)
  let s:=augmentedGeodesics B Γ N D C (AC.complete_domain g n X) LS
  obtain ⟨κ,o,hκ,hκlen,hcover⟩:=exists_actual_cut_of_geodesics A T AC X s
    (fun δ hδ=>augmentedGeodesics_simple B Γ N D C (AC.complete_domain g n X) LS hs hδ)
    (fun δ hδ ε hε hne=>augmentedGeodesics_disjoint B Γ N D C
      (AC.complete_domain g n X) LS hs htrace hδ hε hne)
  refine ⟨s.card,augmentedGeodesics_card_le B Γ N D C (AC.complete_domain g n X) LS,
    κ,o,hκ,?_,?_,?_,hcover⟩
  · rw [hκlen]
    have hh:=augmentedGeodesics_length_le B Γ N D C (AC.complete_domain g n X) LS hΓ
    have he:(∑i,B.curves.length (Γ i))=∑i,H.length (γ i):=by
      apply Finset.sum_congr rfl
      intro i hi
      exact A.length_eq g n X (γ i)
    simpa only [he] using hh
  · intro i hi
    have hm:Γ i∈s:=Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    obtain ⟨e,he⟩:=(hcover (Γ i)).mp hm
    exact ⟨e,(A.primitiveEquiv g n X).injective he⟩
  · intro i hi e
    exact nonisolated_disjoint_augmented B Γ N D C (AC.complete_domain g n X) LS
      hΓ hs htrace i hi ((hcover _).mpr ⟨e,rfl⟩)
end WP.Critical.ShortConfiguration
