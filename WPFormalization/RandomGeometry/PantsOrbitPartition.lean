import WPFormalization.RandomGeometry.PantsOrbitLabels
import WPFormalization.RandomGeometry.PantsStarPlanar
import WPFormalization.RandomGeometry.PantsCutTopology
import WPFormalization.RandomGeometry.PantsFactorialCount

/-! Partition of actual ordered short pants tuples into the classified orbits. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) {g n r : ℕ}

def PantsStarShortTuple (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :=
  Σo : PantsStarOrbit T g n r,
    {γ : Fin r → H.Primitive g n X // T.orbitMem o.val X γ ∧ ∀i, H.length (γ i) ≤ L}

lemma pantsOrbit_curve_planar (hg : 1 ≤ g) (o : PantsStarOrbit T g n r)
    (X : G.Moduli g n (fun _ => 0)) (γ : Fin r → H.Primitive g n X)
    (hγ : T.orbitMem o.val X γ) (i : Fin r) :
    ∃S : Finset (Fin n), H.planarSide (γ i)=some S ∧ S.card=2 := by
  let f := pantsOrbitLabel T o
  let D := pantsCutGraph g n r f
  let S := D.cuspSet {i.succ}
  refine ⟨S,(T.planarSide_iff o.val X γ hγ hg i S).2 ?_,?_⟩
  · exact ((pantsOrbitLabelIso T o).planarSide i S).1 (pantsStar_planarSide g n r f i)
  · exact (pantsStar_leafData g n r f i).two_cusps

def pantsStarShortTupleToActual (hg : 1 ≤ g) (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    PantsStarShortTuple T (r:=r) X L → H.OrderedPlanarTuple X 2 L r := fun p =>
  ⟨p.2.val,T.orbit_injective p.1.val X p.2.val p.2.property.1,fun i =>
    (H.mem_shortPlanar X 2 L (p.2.val i)).2
      ⟨p.2.property.2 i,pantsOrbit_curve_planar T hg p.1 X p.2.val p.2.property.1 i⟩⟩

lemma pantsStarShortTupleToActual_injective (hg : 1 ≤ g)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    Function.Injective (pantsStarShortTupleToActual T hg (r:=r) X L) := by
  rintro ⟨o,a⟩ ⟨p,b⟩ hab
  have hγ : a.val=b.val := congrArg Subtype.val hab
  have hop : o=p := Subtype.ext (orbitMem_unique T o.val p.val X a.val a.property.1
    (hγ ▸ b.property.1))
  subst p
  congr 1
  exact Subtype.ext hγ

include C in
lemma pantsStarShortTupleToActual_surjective (hg : 1 ≤ g) (hr : 0 < r)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (hL : L < 2*Real.arsinh 1) :
    Function.Surjective (pantsStarShortTupleToActual T hg (r:=r) X L) := by
  intro γ
  have hlength : ∀i, H.length (γ.val i) ≤ L :=
    fun i => ((H.mem_shortPlanar X 2 L (γ.val i)).1 (γ.property.2 i)).1
  have htypes : ∀i, ∃S : Finset (Fin n), H.planarSide (γ.val i)=some S ∧ S.card=2 :=
    fun i => ((H.mem_shortPlanar X 2 L (γ.val i)).1 (γ.property.2 i)).2
  choose S hS hcard using htypes
  obtain ⟨o,ho,leaf,hleaf,_⟩ := short_pants_tuple_cut T C hg L hL X γ.val γ.property.1
    hlength S hS hcard
  let e0 : Fin r := ⟨0,hr⟩
  let f := pantsCutLabels (T.cut o) leaf hleaf
  let I := pantsCutStarIso (T.cut o) leaf hleaf (T.cut_connected o) e0 g (T.cut_euler o)
  let p : PantsStarOrbit T g n r := ⟨o,f,⟨I⟩⟩
  exact ⟨⟨p,γ.val,ho,hlength⟩,Subtype.ext rfl⟩

def pantsTuplePartitionEquiv (hg : 1 ≤ g) (hr : 0 < r)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (hL : L < 2*Real.arsinh 1) :
    PantsStarShortTuple T (r:=r) X L ≃ H.OrderedPlanarTuple X 2 L r :=
  Equiv.ofBijective (pantsStarShortTupleToActual T hg X L)
    ⟨pantsStarShortTupleToActual_injective T hg X L,
      pantsStarShortTupleToActual_surjective T C hg hr X L hL⟩

def pantsLengthTest (L : ℝ) (x : Fin r → ℝ) : ℝ≥0∞ := if ∀i, x i ≤ L then 1 else 0

set_option backward.isDefEq.respectTransparency false in
lemma pantsOrbitShort_tsum_one (o : PantsStarOrbit T g n r)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    T.orbitSum o.val (pantsLengthTest L) X =
      ∑' _ : {γ : Fin r → H.Primitive g n X //
        T.orbitMem o.val X γ ∧ ∀i, H.length (γ i) ≤ L}, (1 : ℝ≥0∞) := by
  classical
  let p := fun γ : Fin r → H.Primitive g n X => T.orbitMem o.val X γ
  let q := fun γ : Fin r → H.Primitive g n X => ∀i, H.length (γ i) ≤ L
  have hs := tsum_subtype {γ : Subtype p | q γ.val} (fun _ => (1 : ℝ≥0∞))
  let es : {γ : Subtype p | q γ.val} ≃ {γ : Subtype p // q γ.val} := Equiv.refl _
  have he := (es.trans (Equiv.subtypeSubtypeEquivSubtypeInter p q)).tsum_eq
    (fun _ => (1 : ℝ≥0∞))
  calc
    _ = ∑' γ : Subtype p, if q γ.val then (1 : ℝ≥0∞) else 0 := rfl
    _ = ∑' _ : {γ : Subtype p | q γ.val}, (1 : ℝ≥0∞) := by
      simpa only [Set.indicator,Set.mem_ofPred_eq] using hs.symm
    _ = _ := he

include C in
lemma pants_factorial_orbit_sum (hg : 1 ≤ g) (hr : 0 < r)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (hL : L < 2*Real.arsinh 1) :
    (∑' o : PantsStarOrbit T g n r, T.orbitSum o.val (pantsLengthTest L) X) =
      ((H.pantsCount X L).descFactorial r : ℝ≥0∞) := by
  simp_rw [pantsOrbitShort_tsum_one T]
  rw [← ENNReal.tsum_sigma]
  have he := (pantsTuplePartitionEquiv T C hg hr X L hL).tsum_eq (fun _ => (1 : ℝ≥0∞))
  exact he.trans (H.orderedPantsTuple_tsum_one X L r)

end WP.RandomGeometry
