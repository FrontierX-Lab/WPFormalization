import WPFormalization.Critical.ShortConfigurationRecordingLoopLength
/- Finite actual simple-loop families are straightened and deduplicated
locally into an ACTUAL multicurve orbit of the same A/T model. Positive
homotopy length and the real loop-variation budgets are explicit inputs;
the G.3 RN filling producer is not asserted by this module. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry
open scoped Classical ENNReal

variable (B:BorderedGeometry.{u,v}) (hcomplete:B.surface.domain=univ)
  (H:LoopStraighteningClassics B hcomplete)
  {ι:Type w} [Fintype ι] (f:ι→ClosedLoop B.surface.Point)
  (hsimple:∀i,(f i).Simple) (hpos:∀i,(f i).PositiveHomotopyLength)

def straightenedLoop (i:ι) : B.curves.Primitive :=
  Classical.choose (H.representative (f i) (hsimple i) (hpos i))

lemma straightenedLoop_class (i:ι) :
    (primitiveLoop B (straightenedLoop B hcomplete H f hsimple hpos i)).UnorientedFreelyHomotopic (f i) :=
  Classical.choose_spec (H.representative (f i) (hsimple i) (hpos i))

lemma straightenedLoop_simple (i:ι) :
    SimpleTrace B (straightenedLoop B hcomplete H f hsimple hpos i) :=
  H.simple_representative _ (f i) (hsimple i) (straightenedLoop_class B hcomplete H f hsimple hpos i)

lemma straightenedLoop_length_le (W:ι→ℝ) (hW:∀i,0≤W i)
    (hlen:∀i,(f i).length≤ENNReal.ofReal (W i)) (i:ι) :
    B.curves.length (straightenedLoop B hcomplete H f hsimple hpos i)≤W i := by
  apply (ENNReal.ofReal_le_ofReal_iff (hW i)).mp
  exact (H.length_minimal _ (f i) (straightenedLoop_class B hcomplete H f hsimple hpos i)).trans (hlen i)

def straightenedBoundary : Finset B.curves.Primitive :=
  univ.image (straightenedLoop B hcomplete H f hsimple hpos)

lemma straightenedBoundary_card_le :
    (straightenedBoundary B hcomplete H f hsimple hpos).card≤Fintype.card ι :=
  (Finset.card_image_le).trans_eq (Finset.card_univ)

lemma straightenedBoundary_simple (γ:B.curves.Primitive)
    (hγ:γ∈straightenedBoundary B hcomplete H f hsimple hpos) : SimpleTrace B γ := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hγ
  exact straightenedLoop_simple B hcomplete H f hsimple hpos i

lemma straightenedBoundary_disjoint
    (hdisjoint:∀i j,i≠j→Disjoint (f i).trace (f j).trace)
    {γ δ:B.curves.Primitive}
    (hγ:γ∈straightenedBoundary B hcomplete H f hsimple hpos)
    (hδ:δ∈straightenedBoundary B hcomplete H f hsimple hpos) (hne:γ≠δ) :
    Disjoint (B.curves.trace γ) (B.curves.trace δ) := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hγ
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hδ
  have hij:i≠j := by intro he;subst j;exact hne rfl
  exact (H.disjoint_representatives _ _ (f i) (f j) (hsimple i) (hsimple j)
    (straightenedLoop_class B hcomplete H f hsimple hpos i)
    (straightenedLoop_class B hcomplete H f hsimple hpos j)
    (hdisjoint i j hij)).resolve_left hne

lemma straightenedBoundary_length_le (W:ι→ℝ) (hW:∀i,0≤W i)
    (hlen:∀i,(f i).length≤ENNReal.ofReal (W i)) :
    ∑γ∈straightenedBoundary B hcomplete H f hsimple hpos,B.curves.length γ ≤ ∑i,W i := by
  let q:=straightenedLoop B hcomplete H f hsimple hpos
  have hnonneg : ∀i:ι,0≤B.curves.length (q i) := fun i=>(B.curves.representative (q i)).period_pos.le
  calc
    _ ≤ ∑γ∈straightenedBoundary B hcomplete H f hsimple hpos,
        ∑i∈univ.filter (fun i=>q i=γ),B.curves.length (q i) := by
      apply Finset.sum_le_sum
      intro γ hγ
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hγ
      rw [←he]
      exact Finset.single_le_sum (fun j hj=>hnonneg j) (by simp [q])
    _ = ∑i,B.curves.length (q i) := by
      exact Finset.sum_fiberwise_of_maps_to (s:=univ)
        (t:=straightenedBoundary B hcomplete H f hsimple hpos) (g:=q)
        (fun i hi=>Finset.mem_image.mpr ⟨i,hi,rfl⟩) (fun i=>B.curves.length (q i))
    _ ≤ ∑i,W i := Finset.sum_le_sum (fun i hi=>straightenedLoop_length_le B hcomplete H f hsimple hpos W hW hlen i)

end WP.Critical.ShortConfiguration

namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortLoopStraighteningGeometry
open scoped Classical ENNReal
universe x y z a b
lemma exists_actual_straightened_cut {P:WP.PsiTheory}
    {G:WeilPeterssonGeometry.{x,y} P} {HC:HyperbolicCurveGeometry.{x,y,z} G}
    (A:AmbientRealization HC) (T:MulticurveTopology.{x,y,z,a} G HC)
    (C:AmbientCurveCompatibility A T) {g n:ℕ} (X:G.Moduli g n (fun _=>0))
    (J:LoopStraighteningClassics (A.model g n X) (C.complete_domain g n X))
    {ι:Type b} [Fintype ι] (f:ι→ClosedLoop (A.model g n X).surface.Point)
    (hsimple:∀i,(f i).Simple) (hpos:∀i,(f i).PositiveHomotopyLength)
    (hdisjoint:∀i j,i≠j→Disjoint (f i).trace (f j).trace)
    (W:ι→ℝ) (hW:∀i,0≤W i) (hlen:∀i,(f i).length≤ENNReal.ofReal (W i)) :
    ∃k≤Fintype.card ι,∃κ:Fin k→HC.Primitive g n X,∃o:T.Orbit g n k,
      T.orbitMem o X κ ∧ (∑e,HC.length (κ e))≤∑i,W i ∧
      (∀i,∃e,(primitiveLoop (A.model g n X) (A.primitiveEquiv g n X (κ e))).UnorientedFreelyHomotopic (f i)) ∧
      (∀e,∃i,(primitiveLoop (A.model g n X) (A.primitiveEquiv g n X (κ e))).UnorientedFreelyHomotopic (f i)) := by
  let B:=A.model g n X
  let q:=straightenedLoop B (C.complete_domain g n X) J f hsimple hpos
  let s:=straightenedBoundary B (C.complete_domain g n X) J f hsimple hpos
  let e:Fin s.card≃s:=s.equivFin.symm
  let κ:Fin s.card→HC.Primitive g n X:=fun i=>(A.primitiveEquiv g n X).symm (e i).val
  have hinj:Function.Injective κ := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact (A.primitiveEquiv g n X).symm.injective hij
  have hs:∀i,HC.simple (κ i) := by
    intro i
    apply (C.simple_iff g n X (κ i)).mpr
    simpa [κ] using straightenedBoundary_simple B (C.complete_domain g n X) J f hsimple hpos
      (e i).val (e i).property
  have hd:∀i j,i≠j→T.disjoint (κ i) (κ j) := by
    intro i j hij
    apply (C.disjoint_iff g n X (κ i) (κ j) (hinj.ne hij)).mpr
    simp only [κ,Equiv.apply_symm_apply]
    apply straightenedBoundary_disjoint B (C.complete_domain g n X) J f hsimple hpos hdisjoint
      (e i).property (e j).property
    intro he
    exact hij (e.injective (Subtype.ext he))
  obtain ⟨o,ho,hu⟩:=T.orbit_partition X κ hinj hs hd
  refine ⟨s.card,straightenedBoundary_card_le B (C.complete_domain g n X) J f hsimple hpos,κ,o,ho,?_,?_,?_⟩
  · have hsum: (∑i,HC.length (κ i))=∑γ∈s,B.curves.length γ := by
      calc
        _ =∑i:Fin s.card,B.curves.length (e i).val := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [κ] using (A.length_eq g n X (κ i)).symm
        _ =∑γ:s,B.curves.length γ.val := e.sum_comp (fun γ:s=>B.curves.length γ.val)
        _ =∑γ∈s,B.curves.length γ := Finset.sum_coe_sort s _
    rw [hsum]
    exact straightenedBoundary_length_le B (C.complete_domain g n X) J f hsimple hpos W hW hlen
  · intro i
    have hqi:q i∈s:=Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨j,hj⟩:=e.surjective ⟨q i,hqi⟩
    refine ⟨j,?_⟩
    have hje:(e j).val=q i:=congrArg Subtype.val hj
    simpa [κ,hje] using straightenedLoop_class B (C.complete_domain g n X) J f hsimple hpos i
  · intro j
    obtain ⟨i,hi,he⟩:=Finset.mem_image.mp (e j).property
    refine ⟨i,?_⟩
    have hje:(e j).val=q i:=he.symm
    simpa [κ,hje] using straightenedLoop_class B (C.complete_domain g n X) J f hsimple hpos i
end WP.Critical.ShortConfiguration
