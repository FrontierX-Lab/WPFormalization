import WPFormalization.External.MulticurveRestrictionGeometry
import WPFormalization.Critical.SurvivingMixedCurveTypes
import WPFormalization.Critical.CutGraphData
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External Finset
open scoped Classical
namespace MulticurveCutData.Gluing
variable {n r : ℕ} {D : WP.External.MulticurveCutData n r}
    {E : WP.External.MulticurveCutData n 1} {e : Fin r}

lemma components_ne_one_of_only_edge (R : D.Gluing (singletonEdge e) E)
    (c a : Fin D.components) (hne : a≠c)
    (hinc : ∀p : Fin r×Fin 2,D.edgeVertex p=c → p.1=e) : E.components≠1 := by
  intro hE
  have hmap : R.vertexMap c=R.vertexMap a := by
    apply Fin.ext
    have h0 := (R.vertexMap c).isLt
    have h1 := (R.vertexMap a).isLt
    omega
  have hp := R.fiber_connected c a hmap
  have hstop {b : Fin D.components} (h : Relation.ReflTransGen (D.DeletedAdjacent (singletonEdge e)) c b) : b=c := by
    induction h with
    | refl => rfl
    | @tail b d h hbd ih =>
      obtain ⟨j,hj,hor⟩ := hbd
      have hj' : j≠e := by
        intro he
        apply hj
        exact ⟨0,he.symm⟩
      rcases hor with h0|h1
      · exact (hj' (hinc (j,0) (h0.1.trans ih))).elim
      · exact (hj' (hinc (j,1) (h1.1.trans ih))).elim
  exact hne (hstop hp)
end MulticurveCutData.Gluing

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)

lemma isNonseparating_iff_components {g n : ℕ} {X : G.Moduli g n (fun _ => 0)}
    (o : T.Orbit g n 1) (γ : H.Primitive g n X)
    (ho : T.orbitMem o X (fun _ => γ)) :
    IsNonseparating T γ ↔ (T.cut o).components=1 := by
  constructor
  · rintro ⟨p,hp,hc⟩
    have he : p=o := WP.RandomGeometry.orbitMem_unique T p o X (fun _ => γ) hp ho
    exact he ▸ hc
  · intro hc
    exact ⟨o,ho,hc⟩

lemma actual_nonseparating_not_only_edge (RG : MulticurveRestrictionGeometry G H T)
    {g n r : ℕ} {X : G.Moduli g n (fun _ => 0)} (o : T.Orbit g n r)
    (γ : Fin r → H.Primitive g n X) (ho : T.orbitMem o X γ)
    (e : Fin r) (hnonsep : IsNonseparating T (γ e))
    (c a : Fin (T.cut o).components) (hne : a≠c) :
    ¬ (∀p : Fin r×Fin 2,(T.cut o).edgeVertex p=c → p.1=e) := by
  intro hinc
  let ι := singletonEdge e
  have hmem := RG.orbitMem_restrict ι o X γ ho
  have hc := (isNonseparating_iff_components T (RG.restrictOrbit ι o) (γ e) hmem).mp hnonsep
  obtain ⟨R⟩ := RG.cut_restrict ι o
  exact MulticurveCutData.Gluing.components_ne_one_of_only_edge R c a hne hinc hc
end WP.Critical
