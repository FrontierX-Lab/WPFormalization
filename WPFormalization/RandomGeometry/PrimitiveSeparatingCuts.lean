import WPFormalization.RandomGeometry.PrimitiveOneEdgeClassification
import WPFormalization.Critical.CutGraphData

/-! Actual oriented endpoint allocations of a one-curve separating cut.
The arbitrary incidence orientation only chooses an injection into the ordered
positive-genus sum; no orbit multiplicity is assumed. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Critical Finset
namespace OneEdgeCut
variable {n : ℕ} (D : MulticurveCutData n 1)

def endpointEquiv (hc : D.ConnectedWithin univ) (hQ : D.components=2) :
    Fin 2≃Fin D.components := Equiv.ofBijective (fun j=>D.edgeVertex (0,j)) ⟨by
      intro a b he
      exact congrArg Prod.snd (edgeVertex_injective D hc hQ he),by
      intro c
      rcases vertex_endpoints D hc c with h0|h1
      · exact ⟨0,h0.symm⟩
      · exact ⟨1,h1.symm⟩⟩

@[simp] lemma endpointEquiv_apply (hc : D.ConnectedWithin univ) (hQ : D.components=2)
    (j : Fin 2) : endpointEquiv D hc hQ j=D.edgeVertex (0,j) := rfl

def separatingSkeleton : CutSkeleton 1 2 where
  edgeVertex e:=e.2

def separatingRealization (hc : D.ConnectedWithin univ) (hQ : D.components=2) :
    separatingSkeleton.Realization D where
  vertices := (endpointEquiv D hc hQ).symm
  flip:=fun _=>false
  edge_eq:=by
    intro e j
    have he : e=0 := Subsingleton.elim _ _
    subst e
    exact (endpointEquiv D hc hQ).symm_apply_apply j

lemma endpoint_genus_sum {g : ℕ} (hc : D.ConnectedWithin univ) (hQ : D.components=2)
    (he : (∑c,D.genus c)+1+1=g+D.components) :
    D.genus (D.edgeVertex (0,0))+D.genus (D.edgeVertex (0,1))=g := by
  have hs := Equiv.sum_comp (endpointEquiv D hc hQ) D.genus
  simp only [Fin.sum_univ_two,endpointEquiv_apply] at hs
  omega

end OneEdgeCut
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    {g n : ℕ}

abbrev PrimitiveSeparatingOrbit (g n : ℕ) :=
  {o : T.Orbit g n 1 // (T.cut o).components=2 ∧ ∀c,1≤(T.cut o).genus c}
instance (g n : ℕ) : Fintype (PrimitiveSeparatingOrbit T g n) :=
  inferInstanceAs (Fintype (Subtype _))

def primitiveSeparatingOrbitRealization (o : PrimitiveSeparatingOrbit T g n) :
    OneEdgeCut.separatingSkeleton.Realization (T.cut o.val) :=
  OneEdgeCut.separatingRealization (T.cut o.val) (T.cut_connected o.val) o.property.1

def primitiveSeparatingOrbitGenus (o : PrimitiveSeparatingOrbit T g n) : ℕ :=
  (T.cut o.val).genus ((T.cut o.val).edgeVertex (0,0))

def primitiveSeparatingOrbitCusps (o : PrimitiveSeparatingOrbit T g n) : Fin n→Fin 2 :=
  (primitiveSeparatingOrbitRealization T o).cusps

lemma primitiveSeparatingOrbit_genus_positive (o : PrimitiveSeparatingOrbit T g n) :
    1≤primitiveSeparatingOrbitGenus T o := o.property.2 _

lemma primitiveSeparatingOrbit_genus_lt (o : PrimitiveSeparatingOrbit T g n) :
    primitiveSeparatingOrbitGenus T o<g := by
  have hs := OneEdgeCut.endpoint_genus_sum (T.cut o.val) (T.cut_connected o.val)
    o.property.1 (T.cut_euler o.val)
  have hp := o.property.2 ((T.cut o.val).edgeVertex (0,1))
  change (T.cut o.val).genus ((T.cut o.val).edgeVertex (0,0))<g
  omega

lemma primitiveSeparatingOrbit_genus_second (o : PrimitiveSeparatingOrbit T g n) :
    (primitiveSeparatingOrbitRealization T o).genus 1=g-primitiveSeparatingOrbitGenus T o := by
  have hs := OneEdgeCut.endpoint_genus_sum (T.cut o.val) (T.cut_connected o.val)
    o.property.1 (T.cut_euler o.val)
  change (T.cut o.val).genus ((T.cut o.val).edgeVertex (0,1))=g-
    (T.cut o.val).genus ((T.cut o.val).edgeVertex (0,0))
  omega

lemma primitiveSeparatingOrbitAllocation_injective : Function.Injective
    (fun o : PrimitiveSeparatingOrbit T g n=>
      (primitiveSeparatingOrbitGenus T o,primitiveSeparatingOrbitCusps T o)) := by
  intro o p he
  have hgen : primitiveSeparatingOrbitGenus T o=primitiveSeparatingOrbitGenus T p := congrArg Prod.fst he
  have hcusps := congrArg Prod.snd he
  let Ro := primitiveSeparatingOrbitRealization T o
  let Rp := primitiveSeparatingOrbitRealization T p
  have hg : Ro.genus=Rp.genus := by
    funext c
    fin_cases c
    · exact hgen
    · change (primitiveSeparatingOrbitRealization T o).genus 1=
        (primitiveSeparatingOrbitRealization T p).genus 1
      rw [primitiveSeparatingOrbit_genus_second T,primitiveSeparatingOrbit_genus_second T,hgen]
  have hc : Ro.cusps=Rp.cusps := hcusps
  have io := Ro.isomorphism
  have ip := Rp.isomorphism
  have hcuts : OneEdgeCut.separatingSkeleton.cutData Ro.genus Ro.cusps=
      OneEdgeCut.separatingSkeleton.cutData Rp.genus Rp.cusps := by rw [hg,hc]
  rw [hcuts] at io
  apply Subtype.ext
  exact T.cut_classifies o.val p.val ⟨io.trans ip.symm⟩

def primitiveSeparatingOrbitAllocation (o : PrimitiveSeparatingOrbit T g n) :
    Fin (g-1)×(Fin n→Fin 2) :=
  (⟨primitiveSeparatingOrbitGenus T o-1,by
    have := primitiveSeparatingOrbit_genus_positive T o
    have := primitiveSeparatingOrbit_genus_lt T o
    omega⟩,primitiveSeparatingOrbitCusps T o)

lemma primitiveSeparatingOrbitAllocation_genus (o : PrimitiveSeparatingOrbit T g n) :
    (primitiveSeparatingOrbitAllocation T o).1.val+1=primitiveSeparatingOrbitGenus T o := by
  have := primitiveSeparatingOrbit_genus_positive T o
  change primitiveSeparatingOrbitGenus T o-1+1=_
  omega

lemma primitiveSeparatingOrbitAllocation_finite_injective :
    Function.Injective (primitiveSeparatingOrbitAllocation T : PrimitiveSeparatingOrbit T g n→_) := by
  intro o p he
  apply primitiveSeparatingOrbitAllocation_injective T
  apply Prod.ext
  · have h := congrArg (fun z : Fin (g-1)×(Fin n→Fin 2)=>z.1.val+1) he
    simpa only [primitiveSeparatingOrbitAllocation_genus T] using h
  · have hc := congrArg (fun z : Fin (g-1)×(Fin n→Fin 2)=>z.2) he
    exact hc

end WP.RandomGeometry
