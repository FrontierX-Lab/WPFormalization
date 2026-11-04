import WPFormalization.Critical.SeparatingNonPantsClassification
import WPFormalization.Critical.CutBadTupleCoverIndex
import WPFormalization.Critical.CutRestrictionCombinatorics
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry CutGraphOrbits MeasureTheory Finset
open scoped Classical ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  {g n : ℕ}

def IsSeparatingNonPants {X : G.Moduli g n (fun _ => 0)} (γ : H.Primitive g n X) : Prop :=
  H.simple γ ∧ ¬IsNonseparating T γ ∧
    ¬∃S : Finset (Fin n),H.planarSide γ=some S ∧ S.card=2

abbrev SeparatingNonPantsCurve (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :=
  {γ : H.Primitive g n X // IsSeparatingNonPants T γ ∧ H.length γ≤L}

def separatingNonPantsCount (X : G.Moduli g n (fun _ => 0)) (L : ℝ) : ℝ≥0∞ :=
  ∑' _ : SeparatingNonPantsCurve T X L,(1 : ℝ≥0∞)

abbrev SeparatingNonPantsOrbit (g n : ℕ) :=
  {o : T.Orbit g n 1 // (T.cut o).components≠1 ∧
    ¬∃S : Finset (Fin n),(T.cut o).PlanarSide 0 S ∧ S.card=2}
instance : Fintype (SeparatingNonPantsOrbit T g n) := inferInstanceAs (Fintype (Subtype _))

abbrev SeparatingNonPantsIndex (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :=
  Σo : SeparatingNonPantsOrbit T g n,
    {γ : Fin 1→H.Primitive g n X // T.orbitMem o.val X γ ∧
      (fun i => H.length (γ i))∈cutLengthBox 1 L}

def simpleSingletonOrbit {X : G.Moduli g n (fun _ => 0)}
    (γ : H.Primitive g n X) (hγ : H.simple γ) : T.Orbit g n 1 :=
  Classical.choose (T.orbit_partition X (fun _ => γ) (Function.injective_of_subsingleton _)
    (fun _ => hγ) (by intro i j hij;exact False.elim (hij (Subsingleton.elim _ _))))
lemma simpleSingletonOrbit_mem {X : G.Moduli g n (fun _ => 0)}
    (γ : H.Primitive g n X) (hγ : H.simple γ) :
    T.orbitMem (simpleSingletonOrbit T γ hγ) X (fun _ => γ) :=
  (Classical.choose_spec (T.orbit_partition X (fun _ => γ) (Function.injective_of_subsingleton _)
    (fun _ => hγ) (by intro i j hij;exact False.elim (hij (Subsingleton.elim _ _))))).1

lemma separatingNonPants_iff_orbit (hg : 1≤g) (o : T.Orbit g n 1)
    (X : G.Moduli g n (fun _ => 0)) (γ : H.Primitive g n X)
    (ho : T.orbitMem o X (fun _ => γ)) :
    IsSeparatingNonPants T γ ↔ (T.cut o).components≠1 ∧
      ¬∃S : Finset (Fin n),(T.cut o).PlanarSide 0 S ∧ S.card=2 := by
  constructor
  · intro h
    refine ⟨fun hc => h.2.1 ((isNonseparating_iff_components T o γ ho).mpr hc),?_⟩
    rintro ⟨S,hS,hcard⟩
    exact h.2.2 ⟨S,(T.planarSide_iff o X _ ho hg 0 S).mpr hS,hcard⟩
  · intro h
    refine ⟨T.orbit_simple o X _ ho 0,fun hN => h.1 ((isNonseparating_iff_components T o γ ho).mp hN),?_⟩
    rintro ⟨S,hS,hcard⟩
    exact h.2 ⟨S,(T.planarSide_iff o X _ ho hg 0 S).mp hS,hcard⟩

def separatingNonPantsIndexToCurve (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    SeparatingNonPantsIndex T X L→SeparatingNonPantsCurve T X L := fun j => by
  have he : (fun _ : Fin 1 => j.2.val 0)=j.2.val := by funext i;rw [Fin.eq_zero i]
  have ho : T.orbitMem j.1.val X (fun _ => j.2.val 0) := he ▸ j.2.property.1
  exact ⟨j.2.val 0,(separatingNonPants_iff_orbit T hg j.1.val X _ ho).mpr j.1.property,j.2.property.2.2 0⟩

lemma separatingNonPantsIndexToCurve_injective (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    Function.Injective (separatingNonPantsIndexToCurve T hg X L) := by
  rintro ⟨o,γ⟩ ⟨p,δ⟩ he
  have h0 : γ.val 0=δ.val 0 := congrArg Subtype.val he
  have hv : γ.val=δ.val := by funext i;rw [Fin.eq_zero i];exact h0
  have hop : o=p := Subtype.ext (orbitMem_unique T o.val p.val X γ.val γ.property.1
    (hv ▸ δ.property.1))
  subst p
  congr 1
  exact Subtype.ext hv

lemma separatingNonPantsIndexToCurve_surjective (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    Function.Surjective (separatingNonPantsIndexToCurve T hg X L) := by
  intro γ
  let o := simpleSingletonOrbit T γ.val γ.property.1.1
  have ho : T.orbitMem o X (fun _ => γ.val) := simpleSingletonOrbit_mem T γ.val γ.property.1.1
  have ht := (separatingNonPants_iff_orbit T hg o X γ.val ho).mp γ.property.1
  refine ⟨⟨⟨o,ht⟩,⟨fun _ => γ.val,ho,?_,fun _ => γ.property.2⟩⟩,Subtype.ext rfl⟩
  intro i
  exact (H.length_pos γ.val).le

def separatingNonPantsIndexEquiv (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    SeparatingNonPantsIndex T X L≃SeparatingNonPantsCurve T X L :=
  Equiv.ofBijective (separatingNonPantsIndexToCurve T hg X L)
    ⟨separatingNonPantsIndexToCurve_injective T hg X L,separatingNonPantsIndexToCurve_surjective T hg X L⟩

lemma separatingNonPantsCount_eq_orbitSum (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    separatingNonPantsCount T X L=
      ∑o : SeparatingNonPantsOrbit T g n,T.orbitSum o.val (cutLengthTest 1 L) X := by
  calc
    _ = ∑' _ : SeparatingNonPantsIndex T X L,(1 : ℝ≥0∞) :=
      ((separatingNonPantsIndexEquiv T hg X L).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
    _ = ∑' o : SeparatingNonPantsOrbit T g n,T.orbitSum o.val (cutLengthTest 1 L) X := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro o
      exact (cutOrbitLengthBox_tsum_one T (CutGraphData.actualSkeleton (T.cut o.val))
        ⟨o.val,⟨CutGraphData.actualSkeletonRealization (T.cut o.val)⟩⟩ L X).symm
    _ = _ := tsum_fintype _

lemma separatingNonPantsCount_measurable (MI : MirzakhaniIntegration G H T) (hg : 1≤g) (L : ℝ) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) => separatingNonPantsCount T X L) := by
  simp_rw [separatingNonPantsCount_eq_orbitSum T hg _ L]
  apply Finset.measurable_sum
  intro o ho
  exact MI.orbitSum_measurable o.val _ (cutLengthTest_measurable 1 L)
end WP.Critical
