import WPFormalization.Critical.SurvivingMixedOrbit
import WPFormalization.Critical.SurvivingMixedStable
import WPFormalization.External.MulticurveRestrictionGeometry
import WPFormalization.RandomGeometry.PantsStarPlanar
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry Finset
open scoped Classical

/-- Retain exactly one physical, ordered curve. -/
def singletonEdge {a : ℕ} (e : Fin a) : Fin 1 ↪ Fin a :=
  ⟨fun _ => e,fun _ _ _ => Subsingleton.elim _ _⟩

lemma survivingMixed_restrict_loop_components {g n r k : ℕ} (f : PantsLabels n r)
    (i : Fin k) {D : MulticurveCutData n (r+k)} {E : MulticurveCutData n 1}
    (I : (survivingMixedCutGraph g n r k f).Isomorphism D)
    (R : D.Gluing (singletonEdge (Fin.natAdd r i)) E) : E.components=1 := by
  let root : Fin (survivingMixedCutGraph g n r k f).components := ⟨0,by simp [survivingMixedCutGraph]⟩
  have hp (j : Fin r) : j.castAdd k ∉ Set.range (singletonEdge (Fin.natAdd r i)) := by
    rintro ⟨a,ha⟩
    have hh := congrArg Fin.val ha
    simp only [singletonEdge,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd] at hh
    omega
  have hv (j : Fin r) : R.vertexMap (I.vertexEquiv j.succ)=R.vertexMap (I.vertexEquiv root) := by
    have he := R.deleted_same_vertex (j.castAdd k) (hp j)
    have h0 := I.edge_eq (j.castAdd k) 0
    have h1 := I.edge_eq (j.castAdd k) 1
    cases hb : I.flip (j.castAdd k)
    · simp [hb,survivingMixedCutGraph] at h0 h1
      rw [←h0,←h1] at he
      exact he.symm
    · simp [hb,survivingMixedCutGraph] at h0 h1
      rw [←h0,←h1] at he
      exact he
  have hall (c : Fin D.components) : R.vertexMap c=R.vertexMap (I.vertexEquiv root) := by
    obtain ⟨a,rfl⟩ := I.vertexEquiv.surjective c
    exact Fin.cases rfl hv a
  have he : Fintype.card (Fin E.components)=1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨R.vertexMap (I.vertexEquiv root),?_⟩
    intro c
    obtain ⟨a,rfl⟩ := R.vertex_surjective c
    exact hall a
  simpa using he

lemma survivingMixed_leafData (g n r k : ℕ) (f : PantsLabels n r) (i : Fin r) :
    PantsLeafData (survivingMixedCutGraph g n r k f) (i.castAdd k) i.succ := by
  classical
  refine ⟨by simp [survivingMixedCutGraph],?_,?_,?_⟩
  · simpa [MulticurveCutData.cuspSet,Fintype.card_subtype,survivingMixedCutGraph] using
      (Fintype.card_congr (pantsStarLeafCuspEquiv (g-k) n r f i)).symm
  · ext e
    refine Fin.addCases (fun j => ?_) (fun j => ?_) e
    · simp [MulticurveCutData.internalEdges,survivingMixedCutGraph,(Fin.succ_ne_zero i).symm]
    · simp [MulticurveCutData.internalEdges,survivingMixedCutGraph,(Fin.succ_ne_zero i).symm]
  · ext e
    refine Fin.addCases (fun j => ?_) (fun j => ?_) e
    · simp [MulticurveCutData.crossingEdges,survivingMixedCutGraph,Xor,eq_comm]
    · have he : Fin.natAdd r j ≠ i.castAdd k := by
        intro h
        have hh:=congrArg Fin.val h
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
        omega
      simp [MulticurveCutData.crossingEdges,survivingMixedCutGraph,Xor,(Fin.succ_ne_zero i).symm,he]

lemma survivingMixed_planarSide (g n r k : ℕ) (f : PantsLabels n r) (i : Fin r) :
    (survivingMixedCutGraph g n r k f).PlanarSide (i.castAdd k)
      ((survivingMixedCutGraph g n r k f).cuspSet {i.succ}) := by
  classical
  let D := survivingMixedCutGraph g n r k f
  let leaf : Fin D.components := i.succ
  let root : Fin D.components := ⟨0,by change 0<r+1;omega⟩
  let V := Finset.univ \ ({leaf} : Finset (Fin D.components))
  have hroot : root ∈ V := by
    simp only [V,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_singleton]
    intro h
    have hh:=congrArg Fin.val h
    change 0=i.val+1 at hh
    omega
  have hadj (j : Fin r) (hj : j.succ ∈ V) : D.AdjacentWithin V root j.succ := by
    refine ⟨hroot,hj,j.castAdd k,Or.inl ?_⟩
    constructor <;> simp [D,survivingMixedCutGraph,root]
  have hadj' (j : Fin r) (hj : j.succ ∈ V) : D.AdjacentWithin V j.succ root := by
    refine ⟨hj,hroot,j.castAdd k,Or.inr ?_⟩
    constructor <;> simp [D,survivingMixedCutGraph,root]
  have hr (c : Fin D.components) : c ∈ V → Relation.ReflTransGen (D.AdjacentWithin V) root c := by
    refine Fin.cases (fun _ => Relation.ReflTransGen.refl)
      (fun j hj => Relation.ReflTransGen.single (hadj j hj)) c
  have hr' (c : Fin D.components) : c ∈ V → Relation.ReflTransGen (D.AdjacentWithin V) c root := by
    refine Fin.cases (fun _ => Relation.ReflTransGen.refl)
      (fun j hj => Relation.ReflTransGen.single (hadj' j hj)) c
  have hconn : D.ConnectedWithin V := by
    refine ⟨⟨root,hroot⟩,?_⟩
    intro a ha b hb
    exact (hr' a ha).trans (hr b hb)
  have hsconn : D.ConnectedWithin {leaf} := by
    refine ⟨Finset.singleton_nonempty _,?_⟩
    intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact Relation.ReflTransGen.refl
  have hp := survivingMixed_leafData g n r k f i
  refine ⟨{leaf},⟨Finset.singleton_nonempty _,⟨root,hroot⟩,hp.crossing,hsconn,hconn⟩,?_,rfl⟩
  have hg0 : D.genus leaf=0 := hp.genus_zero
  have hi0 : D.internalEdges {leaf}=∅ := hp.no_internal
  have he : D.genus leaf+(D.internalEdges {leaf}).card+1=1+0 := by rw [hg0,hi0];simp
  simpa only [MulticurveCutData.SideGenus,Finset.sum_singleton,Finset.card_singleton] using he

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)

/-- An actual simple nonseparating primitive: cutting just this actual curve
has one connected component. No graph model or asymptotic is used to define it. -/
def IsNonseparating {g n : ℕ} {X : G.Moduli g n (fun _ => 0)} (γ : H.Primitive g n X) : Prop :=
  ∃ o : T.Orbit g n 1, T.orbitMem o X (fun _ => γ) ∧ (T.cut o).components=1

lemma IsNonseparating.simple {g n : ℕ} {X : G.Moduli g n (fun _ => 0)}
    {γ : H.Primitive g n X} (h : IsNonseparating T γ) : H.simple γ := by
  obtain ⟨o,ho,hc⟩ := h
  exact T.orbit_simple o X (fun _ => γ) ho 0

lemma survivingMixedOrbit_curve_nonseparating (RG : MulticurveRestrictionGeometry G H T)
    {g n r k : ℕ} (o : SurvivingMixedOrbit T g n r k)
    (X : G.Moduli g n (fun _ => 0)) (γ : Fin (r+k) → H.Primitive g n X)
    (hγ : T.orbitMem o.val X γ) (i : Fin k) : IsNonseparating T (γ (Fin.natAdd r i)) := by
  let ι := singletonEdge (Fin.natAdd r i)
  refine ⟨RG.restrictOrbit ι o.val,RG.orbitMem_restrict ι o.val X γ hγ,?_⟩
  obtain ⟨R⟩ := RG.cut_restrict ι o.val
  exact survivingMixed_restrict_loop_components (survivingMixedOrbitLabel T o) i
    (survivingMixedOrbitIso T o) R
lemma survivingMixedOrbit_curve_pants {g n r k : ℕ} (hg : 1≤g)
    (o : SurvivingMixedOrbit T g n r k)
    (X : G.Moduli g n (fun _ => 0)) (γ : Fin (r+k) → H.Primitive g n X)
    (hγ : T.orbitMem o.val X γ) (i : Fin r) :
    ∃S : Finset (Fin n), H.planarSide (γ (i.castAdd k))=some S ∧ S.card=2 := by
  let f := survivingMixedOrbitLabel T o
  let D := survivingMixedCutGraph g n r k f
  let S := D.cuspSet {i.succ}
  refine ⟨S,(T.planarSide_iff o.val X γ hγ hg (i.castAdd k) S).2 ?_,?_⟩
  · exact ((survivingMixedOrbitIso T o).planarSide (i.castAdd k) S).1
      (survivingMixed_planarSide g n r k f i)
  · exact (survivingMixed_leafData g n r k f i).two_cusps

lemma IsNonseparating.no_planarSide {g n : ℕ} (hg : 1≤g)
    {X : G.Moduli g n (fun _ => 0)} {γ : H.Primitive g n X}
    (h : IsNonseparating T γ) : H.planarSide γ=none := by
  obtain ⟨o,ho,hc⟩ := h
  cases hs : H.planarSide γ with
  | none => rfl
  | some S =>
    obtain ⟨U,hside,hgen,hcusps⟩ := (T.planarSide_iff o X (fun _ => γ) ho hg 0 S).mp hs
    obtain ⟨a,ha⟩ := hside.1
    obtain ⟨b,hb⟩ := hside.2.1
    have hab : a=b := by
      apply Fin.ext
      have ha0 := a.isLt
      have hb0 := b.isLt
      omega
    subst b
    exact (Finset.mem_sdiff.mp hb).2 ha |>.elim

end WP.Critical
