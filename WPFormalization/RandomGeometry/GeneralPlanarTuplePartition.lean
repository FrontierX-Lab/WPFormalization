import WPFormalization.RandomGeometry.GeneralPlanarStarOrbits
import WPFormalization.RandomGeometry.PantsWindowMoments

/-! Complete actual short planar tuple partition. General planar tuples include
nested configurations; stars are only one explicitly defined subfamily. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) {g n r : ℕ}

def OrderedGeneralPlanarTuple (X : G.Moduli g n (fun _ => 0))
    (k : Fin r → ℕ) (L : ℝ) :=
  {γ : Fin r → H.Primitive g n X // Function.Injective γ ∧
    ∀i, γ i ∈ H.shortPlanar X (k i) L}

instance orderedGeneralPlanarTupleFinite (X : G.Moduli g n (fun _ => 0))
    (k : Fin r → ℕ) (L : ℝ) : Finite (OrderedGeneralPlanarTuple (H:=H) X k L) := by
  let f : OrderedGeneralPlanarTuple (H:=H) X k L →
      ∀i,{γ // γ∈H.shortPlanar X (k i) L} := fun γ i => ⟨γ.val i,γ.property.2 i⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun hab i)

instance orderedGeneralPlanarTupleFintype (X : G.Moduli g n (fun _ => 0))
    (k : Fin r → ℕ) (L : ℝ) : Fintype (OrderedGeneralPlanarTuple (H:=H) X k L) :=
  Fintype.ofFinite _

def GeneralPlanarOrbit (g n r : ℕ) (k : Fin r → ℕ) :=
  {o : T.Orbit g n r // ∀i,∃S : Finset (Fin n),
    (T.cut o).PlanarSide i S ∧ S.card=k i}

instance (k : Fin r → ℕ) : Fintype (GeneralPlanarOrbit T g n r k) := by
  classical
  unfold GeneralPlanarOrbit
  infer_instance

def GeneralPlanarShortTuple (X : G.Moduli g n (fun _ => 0))
    (k : Fin r → ℕ) (L : ℝ) :=
  Σo : GeneralPlanarOrbit T g n r k,
    {γ : Fin r → H.Primitive g n X // T.orbitMem o.val X γ ∧∀i,H.length (γ i)≤L}

lemma generalPlanarOrbit_curve_planar (hg : 1≤g) (k : Fin r → ℕ)
    (o : GeneralPlanarOrbit T g n r k) (X : G.Moduli g n (fun _ => 0))
    (γ : Fin r → H.Primitive g n X) (hγ : T.orbitMem o.val X γ) (i : Fin r) :
    ∃S : Finset (Fin n),H.planarSide (γ i)=some S ∧S.card=k i := by
  obtain ⟨S,hS,hcard⟩ := o.property i
  exact ⟨S,(T.planarSide_iff o.val X γ hγ hg i S).2 hS,hcard⟩

def generalPlanarShortTupleToActual (hg : 1≤g) (X : G.Moduli g n (fun _ => 0))
    (k : Fin r → ℕ) (L : ℝ) :
    GeneralPlanarShortTuple T X k L → OrderedGeneralPlanarTuple (H:=H) X k L := fun p =>
  ⟨p.2.val,T.orbit_injective p.1.val X p.2.val p.2.property.1,fun i =>
    (H.mem_shortPlanar X (k i) L (p.2.val i)).2
      ⟨p.2.property.2 i,generalPlanarOrbit_curve_planar T hg k p.1 X p.2.val p.2.property.1 i⟩⟩

lemma generalPlanarShortTupleToActual_injective (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ) :
    Function.Injective (generalPlanarShortTupleToActual T hg X k L) := by
  rintro ⟨o,a⟩ ⟨p,b⟩ hab
  have hγ : a.val=b.val := congrArg Subtype.val hab
  have hop : o=p := Subtype.ext (orbitMem_unique T o.val p.val X a.val a.property.1
    (hγ ▸ b.property.1))
  subst p
  congr 1
  exact Subtype.ext hγ

include C in
lemma generalPlanarShortTupleToActual_surjective (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) :
    Function.Surjective (generalPlanarShortTupleToActual T hg X k L) := by
  intro γ
  have hlength : ∀i,H.length (γ.val i)≤L :=
    fun i => ((H.mem_shortPlanar X (k i) L (γ.val i)).1 (γ.property.2 i)).1
  have hsimple : ∀i,H.simple (γ.val i) :=
    fun i => C.shortPrimitive_simple _ ((hlength i).trans_lt hL)
  have hdis : ∀i j,i≠j →T.disjoint (γ.val i) (γ.val j) := by
    intro i j hij
    exact C.shortSimple_disjoint _ _ (fun h => hij (γ.property.1 h))
      (hsimple i) (hsimple j) ((hlength i).trans_lt hL) ((hlength j).trans_lt hL)
  obtain ⟨o,ho,_⟩ := T.orbit_partition X γ.val γ.property.1 hsimple hdis
  have htype : ∀i,∃S : Finset (Fin n),(T.cut o).PlanarSide i S ∧S.card=k i := by
    intro i
    obtain ⟨S,hS,hcard⟩ := ((H.mem_shortPlanar X (k i) L (γ.val i)).1 (γ.property.2 i)).2
    exact ⟨S,(T.planarSide_iff o X γ.val ho hg i S).1 hS,hcard⟩
  exact ⟨⟨⟨o,htype⟩,γ.val,ho,hlength⟩,Subtype.ext rfl⟩

include C in
def generalPlanarTuplePartitionEquiv (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (k : Fin r → ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) :
    GeneralPlanarShortTuple T X k L ≃ OrderedGeneralPlanarTuple (H:=H) X k L :=
  Equiv.ofBijective (generalPlanarShortTupleToActual T hg X k L)
    ⟨generalPlanarShortTupleToActual_injective T hg X k L,
      generalPlanarShortTupleToActual_surjective T C hg X k L hL⟩

lemma generalPlanarStarOrbit_typed (g n r : ℕ) (k : Fin r → ℕ)
    (o : GeneralPlanarStarOrbit T g n r k) :
    ∀i,∃S : Finset (Fin n),(T.cut o.val).PlanarSide i S ∧S.card=k i := by
  intro i
  let f := generalPlanarOrbitLabel T o
  refine ⟨f.labelSet i,?_,f.labelSet_card i⟩
  exact ((generalPlanarOrbitLabelIso T o).planarSide i (f.labelSet i)).1
    (generalPlanarStarCut_planarSide g n r k f i)

def generalPlanarStarOrbitEmbedding (g n r : ℕ) (k : Fin r → ℕ) :
    GeneralPlanarStarOrbit T g n r k ↪ GeneralPlanarOrbit T g n r k where
  toFun o := ⟨o.val,generalPlanarStarOrbit_typed T g n r k o⟩
  inj' a b h := Subtype.ext (congrArg (fun o : GeneralPlanarOrbit T g n r k => o.val) h)
end WP.RandomGeometry
