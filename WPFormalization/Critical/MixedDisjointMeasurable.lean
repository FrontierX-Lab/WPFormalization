import WPFormalization.Critical.MixedGeometricTuples
import WPFormalization.Critical.CutRestrictionCombinatorics
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory
open scoped Classical ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (RG : MulticurveRestrictionGeometry G H T) {g n r k : ℕ}

def MixedOrbitType (o : T.Orbit g n (r+k)) : Prop :=
  (∀i : Fin r,∃S : Finset (Fin n),(T.cut o).PlanarSide (i.castAdd k) S ∧ S.card=2) ∧
  (∀i : Fin k,(T.cut (RG.restrictOrbit (singletonEdge (Fin.natAdd r i)) o)).components=1)

lemma mixedCurveTypes_iff_orbitType (hg : 1≤g) (o : T.Orbit g n (r+k))
    (X : G.Moduli g n (fun _ => 0)) (γ : Fin (r+k)→H.Primitive g n X)
    (ho : T.orbitMem o X γ) : MixedCurveTypes T γ ↔ MixedOrbitType T RG o := by
  constructor
  · intro h
    constructor
    · intro i
      obtain ⟨S,hS,hcard⟩ := h.1 i
      exact ⟨S,(T.planarSide_iff o X γ ho hg _ S).mp hS,hcard⟩
    · intro i
      exact (isNonseparating_iff_components T _ _
        (RG.orbitMem_restrict (singletonEdge (Fin.natAdd r i)) o X γ ho)).mp (h.2 i)
  · intro h
    constructor
    · intro i
      obtain ⟨S,hS,hcard⟩ := h.1 i
      exact ⟨S,(T.planarSide_iff o X γ ho hg _ S).mpr hS,hcard⟩
    · intro i
      exact (isNonseparating_iff_components T _ _
        (RG.orbitMem_restrict (singletonEdge (Fin.natAdd r i)) o X γ ho)).mpr (h.2 i)

abbrev MixedTypedOrbit (g n r k : ℕ) := {o : T.Orbit g n (r+k) // MixedOrbitType T RG o}
instance : Fintype (MixedTypedOrbit T RG g n r k) := inferInstanceAs (Fintype (Subtype _))

abbrev MixedTypedWindowIndex (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k)→Set ℝ) :=
  Σo : MixedTypedOrbit T RG g n r k,
    {γ : Fin (r+k)→H.Primitive g n X // T.orbitMem o.val X γ ∧ ∀i,H.length (γ i)∈I i}

def mixedTypedIndexToTuple (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k)→Set ℝ) :
    MixedTypedWindowIndex T RG X I→{γ : MixedWindowTuple T X I // TupleDisjoint T γ.val} := fun j =>
  ⟨⟨j.2.val,T.orbit_injective j.1.val X j.2.val j.2.property.1,
    (mixedCurveTypes_iff_orbitType T RG hg j.1.val X j.2.val j.2.property.1).mpr j.1.property,
    j.2.property.2⟩,T.orbit_disjoint j.1.val X j.2.val j.2.property.1⟩

lemma mixedTypedIndexToTuple_injective (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k)→Set ℝ) :
    Function.Injective (mixedTypedIndexToTuple T RG hg X I) := by
  rintro ⟨o,γ⟩ ⟨p,δ⟩ he
  have hv : γ.val=δ.val := congrArg (fun a => a.val.val) he
  have hop : o=p := Subtype.ext (orbitMem_unique T o.val p.val X γ.val γ.property.1
    (hv ▸ δ.property.1))
  subst p
  congr 1
  exact Subtype.ext hv

lemma mixedTypedIndexToTuple_surjective (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k)→Set ℝ) :
    Function.Surjective (mixedTypedIndexToTuple T RG hg X I) := by
  rintro ⟨γ,hd⟩
  obtain ⟨o,ho,hunique⟩ := T.orbit_partition X γ.val γ.property.1 (γ.property.2.1.simple T) hd
  have ht : MixedOrbitType T RG o :=
    (mixedCurveTypes_iff_orbitType T RG hg o X γ.val ho).mp γ.property.2.1
  exact ⟨⟨⟨o,ht⟩,⟨γ.val,ho,γ.property.2.2⟩⟩,Subtype.ext (Subtype.ext rfl)⟩

def mixedTypedIndexEquiv (hg : 1≤g) (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k)→Set ℝ) :
    MixedTypedWindowIndex T RG X I≃{γ : MixedWindowTuple T X I // TupleDisjoint T γ.val} :=
  Equiv.ofBijective (mixedTypedIndexToTuple T RG hg X I)
    ⟨mixedTypedIndexToTuple_injective T RG hg X I,mixedTypedIndexToTuple_surjective T RG hg X I⟩

lemma orbitWindow_tsum_one (o : T.Orbit g n (r+k))
    (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k)→Set ℝ) :
    T.orbitSum o (survivingMixedWindowTest I) X=
      ∑' _ : {γ : Fin (r+k)→H.Primitive g n X // T.orbitMem o X γ ∧ ∀i,H.length (γ i)∈I i},(1 : ℝ≥0∞) := by
  let p := fun γ : Fin (r+k)→H.Primitive g n X => T.orbitMem o X γ
  let q := fun γ : Fin (r+k)→H.Primitive g n X => ∀i,H.length (γ i)∈I i
  have hs := tsum_subtype {γ : Subtype p | q γ.val} (fun _ => (1 : ℝ≥0∞))
  let e : {γ : Subtype p | q γ.val}≃{γ : Subtype p // q γ.val} := Equiv.refl _
  have he := (e.trans (Equiv.subtypeSubtypeEquivSubtypeInter p q)).tsum_eq (fun _ => (1 : ℝ≥0∞))
  calc
    _ = ∑' γ : Subtype p,if q γ.val then (1 : ℝ≥0∞) else 0 := rfl
    _ = ∑' _ : {γ : Subtype p | q γ.val},(1 : ℝ≥0∞) := by
      simpa only [Set.indicator,Set.mem_ofPred_eq] using hs.symm
    _ = _ := he

lemma mixedDisjointWindowTupleCount_eq_orbitSum (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k)→Set ℝ) :
    mixedDisjointWindowTupleCount T X I=
      ∑o : MixedTypedOrbit T RG g n r k,T.orbitSum o.val (survivingMixedWindowTest I) X := by
  calc
    _ = ∑' _ : MixedTypedWindowIndex T RG X I,(1 : ℝ≥0∞) :=
      ((mixedTypedIndexEquiv T RG hg X I).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
    _ = ∑' o : MixedTypedOrbit T RG g n r k,T.orbitSum o.val (survivingMixedWindowTest I) X := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro o
      exact (orbitWindow_tsum_one T o.val X I).symm
    _ = _ := tsum_fintype _

include RG in
lemma mixedDisjointWindowTupleCount_measurable (MI : MirzakhaniIntegration G H T) (hg : 1≤g)
    (I : Fin (r+k)→Set ℝ) (hI : ∀i,MeasurableSet (I i)) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) => mixedDisjointWindowTupleCount T X I) := by
  simp_rw [mixedDisjointWindowTupleCount_eq_orbitSum T RG hg _ I]
  apply Finset.measurable_sum
  intro o ho
  exact MI.orbitSum_measurable _ _ (survivingMixedWindowTest_measurable I hI)
end WP.Critical
