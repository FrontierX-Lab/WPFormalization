import WPFormalization.Critical.SurvivingMixedClassification
import WPFormalization.Critical.SurvivingMixedWindow
import WPFormalization.Critical.CutCanonicalPartition
import WPFormalization.RandomGeometry.PantsMixedFactorialCount
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry Finset
open scoped Classical ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    {g n r k : ℕ}

def MixedCurveTypes {X : G.Moduli g n (fun _ => 0)} (γ : Fin (r+k) → H.Primitive g n X) : Prop :=
  (∀i : Fin r,∃S : Finset (Fin n),H.planarSide (γ (i.castAdd k))=some S ∧ S.card=2) ∧
  (∀i : Fin k,IsNonseparating T (γ (Fin.natAdd r i)))

lemma MixedCurveTypes.simple {X : G.Moduli g n (fun _ => 0)}
    {γ : Fin (r+k) → H.Primitive g n X} (h : MixedCurveTypes T γ) : ∀e,H.simple (γ e) := by
  intro e
  refine Fin.addCases (fun i => ?_) (fun i => ?_) e
  · obtain ⟨S,hS,hcard⟩ := h.1 i
    exact H.planar_simple _ _ hS
  · exact IsNonseparating.simple T (h.2 i)

abbrev MixedWindowTuple (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :=
  {γ : Fin (r+k) → H.Primitive g n X //
    Function.Injective γ ∧ MixedCurveTypes T γ ∧ ∀i,H.length (γ i)∈I i}

def TupleDisjoint {X : G.Moduli g n (fun _ => 0)} (γ : Fin (r+k) → H.Primitive g n X) : Prop :=
  ∀i j,i≠j → T.disjoint (γ i) (γ j)

def mixedWindowTupleCount (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) : ℝ≥0∞ :=
  ∑' _ : MixedWindowTuple T X I,(1 : ℝ≥0∞)
def mixedDisjointWindowTupleCount (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) : ℝ≥0∞ :=
  ∑' _ : {γ : MixedWindowTuple T X I // TupleDisjoint T γ.val},(1 : ℝ≥0∞)
def mixedIntersectingWindowTupleCount (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) : ℝ≥0∞ :=
  ∑' _ : {γ : MixedWindowTuple T X I // ¬TupleDisjoint T γ.val},(1 : ℝ≥0∞)

lemma mixedWindowTupleCount_split (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    mixedWindowTupleCount T X I=mixedDisjointWindowTupleCount T X I+mixedIntersectingWindowTupleCount T X I := by
  have he := (Equiv.sumCompl (fun γ : MixedWindowTuple T X I => TupleDisjoint T γ.val)).tsum_eq
    (fun _ => (1 : ℝ≥0∞))
  rw [ENNReal.summable.tsum_sum ENNReal.summable] at he
  exact he.symm

noncomputable def mixedDisjointOrbit {X : G.Moduli g n (fun _ => 0)}
    (γ : Fin (r+k) → H.Primitive g n X) (hi : Function.Injective γ)
    (ht : MixedCurveTypes T γ) (hd : TupleDisjoint T γ) : T.Orbit g n (r+k) :=
  Classical.choose (T.orbit_partition X γ hi (MixedCurveTypes.simple T ht) hd)
lemma mixedDisjointOrbit_mem {X : G.Moduli g n (fun _ => 0)}
    (γ : Fin (r+k) → H.Primitive g n X) (hi : Function.Injective γ)
    (ht : MixedCurveTypes T γ) (hd : TupleDisjoint T γ) :
    T.orbitMem (mixedDisjointOrbit T γ hi ht hd) X γ :=
  (Classical.choose_spec (T.orbit_partition X γ hi (MixedCurveTypes.simple T ht) hd)).1

def IsSurvivingTuple {X : G.Moduli g n (fun _ => 0)}
    (γ : Fin (r+k) → H.Primitive g n X) : Prop :=
  ∃o : SurvivingMixedOrbit T g n r k,T.orbitMem o.val X γ

lemma mixedDisjointOrbit_surviving_iff {X : G.Moduli g n (fun _ => 0)}
    (γ : Fin (r+k) → H.Primitive g n X) (hi : Function.Injective γ)
    (ht : MixedCurveTypes T γ) (hd : TupleDisjoint T γ) :
    IsSurvivingTuple T γ ↔ ∃f : PantsLabels n r,
      Nonempty ((survivingMixedCutGraph g n r k f).Isomorphism
        (T.cut (mixedDisjointOrbit T γ hi ht hd))) := by
  constructor
  · rintro ⟨o,ho⟩
    have he := orbitMem_unique T o.val (mixedDisjointOrbit T γ hi ht hd) X γ ho
      (mixedDisjointOrbit_mem T γ hi ht hd)
    obtain ⟨f,hf⟩ := o.property
    exact he ▸ ⟨f,hf⟩
  · intro hf
    exact ⟨⟨mixedDisjointOrbit T γ hi ht hd,hf⟩,mixedDisjointOrbit_mem T γ hi ht hd⟩

lemma nonsurviving_canonicalPartition_bad (RG : MulticurveRestrictionGeometry G H T)
    (hg : 1≤g) (htotal : 1≤r+k) {X : G.Moduli g n (fun _ => 0)}
    (γ : Fin (r+k) → H.Primitive g n X) (hi : Function.Injective γ)
    (ht : MixedCurveTypes T γ) (hd : TupleDisjoint T γ) (hbad : ¬IsSurvivingTuple T γ) :
    CutGraphData.baseStableCount (T.cut (mixedDisjointOrbit T γ hi ht hd))≠1 ∨
      CutGraphData.twoCount (T.cut (mixedDisjointOrbit T γ hi ht hd))≠0 := by
  by_contra hb
  push Not at hb
  let o := mixedDisjointOrbit T γ hi ht hd
  have hpart := CutGraphData.has_canonicalPartition (T.cut o) htotal (T.cut_connected o)
  rw [hb.1,hb.2] at hpart
  have hs := survivingMixed_classify_partition T RG o γ (mixedDisjointOrbit_mem T γ hi ht hd)
    hg (CutGraphData.oneCount (T.cut o)) hpart ht.1 ht.2
  exact hbad ((mixedDisjointOrbit_surviving_iff T γ hi ht hd).mpr hs)
def mixedSurvivingWindowTupleCount (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) : ℝ≥0∞ :=
  ∑' _ : {γ : MixedWindowTuple T X I // IsSurvivingTuple T γ.val},(1 : ℝ≥0∞)
def mixedBadDisjointWindowTupleCount (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) : ℝ≥0∞ :=
  ∑' _ : {γ : MixedWindowTuple T X I // TupleDisjoint T γ.val ∧ ¬IsSurvivingTuple T γ.val},(1 : ℝ≥0∞)

abbrev SurvivingWindowIndex (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :=
  Σo : SurvivingMixedOrbit T g n r k,
    {γ : Fin (r+k) → H.Primitive g n X // T.orbitMem o.val X γ ∧ ∀i,H.length (γ i)∈I i}

def survivingWindowIndexToTuple (RG : MulticurveRestrictionGeometry G H T) (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    SurvivingWindowIndex T X I → {γ : MixedWindowTuple T X I // IsSurvivingTuple T γ.val} := fun j =>
  ⟨⟨j.2.val,T.orbit_injective j.1.val X j.2.val j.2.property.1,
    ⟨fun i => survivingMixedOrbit_curve_pants T hg j.1 X j.2.val j.2.property.1 i,
     fun i => survivingMixedOrbit_curve_nonseparating T RG j.1 X j.2.val j.2.property.1 i⟩,
    j.2.property.2⟩,j.1,j.2.property.1⟩

lemma survivingWindowIndexToTuple_injective (RG : MulticurveRestrictionGeometry G H T) (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    Function.Injective (survivingWindowIndexToTuple T RG hg X I) := by
  rintro ⟨o,γ⟩ ⟨p,δ⟩ he
  have hv : γ.val=δ.val := congrArg (fun a => a.val.val) he
  have hop : o=p := Subtype.ext (orbitMem_unique T o.val p.val X γ.val γ.property.1
    (hv ▸ δ.property.1))
  subst p
  congr 1
  exact Subtype.ext hv

lemma survivingWindowIndexToTuple_surjective (RG : MulticurveRestrictionGeometry G H T) (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    Function.Surjective (survivingWindowIndexToTuple T RG hg X I) := by
  rintro ⟨γ,o,ho⟩
  exact ⟨⟨o,⟨γ.val,ho,γ.property.2.2⟩⟩,Subtype.ext (Subtype.ext rfl)⟩

def survivingWindowIndexEquiv (RG : MulticurveRestrictionGeometry G H T) (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    SurvivingWindowIndex T X I ≃ {γ : MixedWindowTuple T X I // IsSurvivingTuple T γ.val} :=
  Equiv.ofBijective (survivingWindowIndexToTuple T RG hg X I)
    ⟨survivingWindowIndexToTuple_injective T RG hg X I,survivingWindowIndexToTuple_surjective T RG hg X I⟩

lemma survivingMixedOrbitWindow_tsum_one (o : SurvivingMixedOrbit T g n r k)
    (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    T.orbitSum o.val (survivingMixedWindowTest I) X=
      ∑' _ : {γ : Fin (r+k) → H.Primitive g n X // T.orbitMem o.val X γ ∧ ∀i,H.length (γ i)∈I i},(1 : ℝ≥0∞) := by
  let p := fun γ : Fin (r+k) → H.Primitive g n X => T.orbitMem o.val X γ
  let q := fun γ : Fin (r+k) → H.Primitive g n X => ∀i,H.length (γ i)∈I i
  have hs := tsum_subtype {γ : Subtype p | q γ.val} (fun _ => (1 : ℝ≥0∞))
  let e : {γ : Subtype p | q γ.val} ≃ {γ : Subtype p // q γ.val} := Equiv.refl _
  have he := (e.trans (Equiv.subtypeSubtypeEquivSubtypeInter p q)).tsum_eq (fun _ => (1 : ℝ≥0∞))
  calc
    _ = ∑' γ : Subtype p,if q γ.val then (1 : ℝ≥0∞) else 0 := rfl
    _ = ∑' _ : {γ : Subtype p | q γ.val},(1 : ℝ≥0∞) := by
      simpa only [Set.indicator,Set.mem_ofPred_eq] using hs.symm
    _ = _ := he

lemma mixedSurvivingWindowTupleCount_eq (RG : MulticurveRestrictionGeometry G H T) (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (I : Fin (r+k) → Set ℝ) :
    mixedSurvivingWindowTupleCount T X I=
      survivingMixedOrbitSum T (survivingMixedWindowTest I) X := by
  calc
    _ = ∑' _ : SurvivingWindowIndex T X I,(1 : ℝ≥0∞) :=
      ((survivingWindowIndexEquiv T RG hg X I).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
    _ = ∑' o : SurvivingMixedOrbit T g n r k,T.orbitSum o.val (survivingMixedWindowTest I) X := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro o
      exact (survivingMixedOrbitWindow_tsum_one T o X I).symm
    _ = _ := tsum_fintype _
end WP.Critical
