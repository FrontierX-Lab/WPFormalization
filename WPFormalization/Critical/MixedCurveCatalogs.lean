import WPFormalization.Critical.NonseparatingPointCounts
import WPFormalization.RandomGeometry.PantsMixedFactorialCount
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory Finset Set
open scoped Classical ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    {g n : ℕ}

def ColoredCurveType {X : G.Moduli g n (fun _ => 0)} (color : Bool) (γ : H.Primitive g n X) : Prop :=
  if color then ∃S : Finset (Fin n),H.planarSide γ=some S ∧ S.card=2 else IsNonseparating T γ

def coloredLengthPointMeasure (X : G.Moduli g n (fun _ => 0)) (color : Bool) :
    WP.Probability.PointMeasure ℝ≥0 :=
  curveLengthPointMeasure H X 1 (by norm_num) (ColoredCurveType T color)

lemma coloredLengthPointMeasure_pants (X : G.Moduli g n (fun _ => 0)) :
    coloredLengthPointMeasure T X true=planarLengthPointMeasure H X 1 (by norm_num) 2 := rfl
lemma coloredLengthPointMeasure_nonsep (X : G.Moduli g n (fun _ => 0)) :
    coloredLengthPointMeasure T X false=nonseparatingLengthPointMeasure T X := rfl

lemma coloredCurveTypes_disjoint (hg : 1≤g) {X : G.Moduli g n (fun _ => 0)}
    {γ : H.Primitive g n X} (hN : ColoredCurveType T false γ)
    (hP : ColoredCurveType T true γ) : False := by
  obtain ⟨S,hS,hcard⟩ := hP
  have hn := IsNonseparating.no_planarSide T hg hN
  rw [hn] at hS
  cases hS

lemma physicalLength_mem_image {X : G.Moduli g n (fun _ => 0)}
    (γ : H.Primitive g n X) (B : Set ℝ≥0) :
    H.length γ ∈ NNReal.toReal '' B ↔ Real.toNNReal (H.length γ)∈B := by
  constructor
  · rintro ⟨b,hb,hbℓ⟩
    rw [←hbℓ]
    simpa using hb
  · intro h
    exact ⟨Real.toNNReal (H.length γ),h,Real.coe_toNNReal _ (H.length_pos γ).le⟩

def mixedCurveWindowCatalog (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (color : Bool) (I : Set ℝ) : Finset (H.Primitive g n X) :=
  (H.shortPrimitive X L).filter (fun γ => ColoredCurveType T color γ ∧ H.length γ∈I)

lemma mem_mixedCurveWindowCatalog (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (color : Bool) (I : Set ℝ) (γ : H.Primitive g n X) :
    γ∈mixedCurveWindowCatalog T X L color I ↔
      H.length γ≤L ∧ ColoredCurveType T color γ ∧ H.length γ∈I := by
  simp only [mixedCurveWindowCatalog,mem_filter,H.mem_shortPrimitive]

lemma mixedCurveWindowCatalog_disjoint {ι : Type*} (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (color : ι→Bool) (I : ι→Set ℝ)
    (hI : ∀i j,i≠j → color i=color j → Disjoint (I i) (I j)) :
    Pairwise (fun i j => Disjoint (mixedCurveWindowCatalog T X L (color i) (I i))
      (mixedCurveWindowCatalog T X L (color j) (I j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro γ hi hj
  have hi' := (mem_mixedCurveWindowCatalog T X L (color i) (I i) γ).mp hi
  have hj' := (mem_mixedCurveWindowCatalog T X L (color j) (I j) γ).mp hj
  by_cases hc : color i=color j
  · exact Set.disjoint_left.mp (hI i j hij hc) hi'.2.2 hj'.2.2
  · cases hci : color i <;> cases hcj : color j
    · exact hc (hci.trans hcj.symm)
    · exact coloredCurveTypes_disjoint T hg (by simpa [hci] using hi'.2.1) (by simpa [hcj] using hj'.2.1)
    · exact coloredCurveTypes_disjoint T hg (by simpa [hcj] using hj'.2.1) (by simpa [hci] using hi'.2.1)
    · exact hc (hci.trans hcj.symm)

lemma coloredLengthPointMeasure_count_eq_catalog (X : G.Moduli g n (fun _ => 0))
    (color : Bool) (B : WP.Probability.RelCompactBorelWindow ℝ≥0)
    (L : ℝ) (hBL : ∀b∈B.carrier,(b:ℝ)≤L) :
    (coloredLengthPointMeasure T X color).count ℝ≥0 B=
      (mixedCurveWindowCatalog T X L color (NNReal.toReal '' B.carrier)).card := by
  let p : H.Primitive g n X → Prop := ColoredCurveType T color
  letI := curveNNLengthMeasure_finite_window H X 1 (by norm_num) p B.carrier
    (B.compactClosure.bddAbove.mono subset_closure)
  apply Nat.cast_injective (R := ℝ≥0∞)
  rw [←(coloredLengthPointMeasure T X color).count_spec ℝ≥0 B]
  change curveNNLengthMeasure H X 1 p B.carrier=_
  rw [curveNNLengthMeasure,sum_dirac_apply_eq_natCard _ _ B.measurableSet]
  have hc : Nat.card {γ : H.Primitive g n X // γ∈mixedCurveWindowCatalog T X L color (NNReal.toReal '' B.carrier)}=
      (mixedCurveWindowCatalog T X L color (NNReal.toReal '' B.carrier)).card := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
  rw [←hc]
  congr 1
  apply Nat.card_congr
  refine {
    toFun := fun γ => ⟨γ.val.val,(mem_mixedCurveWindowCatalog T X L color _ γ.val.val).mpr ?_⟩
    invFun := fun γ => ⟨⟨γ.val,((mem_mixedCurveWindowCatalog T X L color _ γ.val).mp γ.property).2.1⟩,?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  · have hb : Real.toNNReal (H.length γ.val.val)∈B.carrier := by simpa only [one_mul] using γ.property
    refine ⟨?_,γ.val.property,(physicalLength_mem_image γ.val.val B.carrier).mpr hb⟩
    have hh:=hBL (Real.toNNReal (H.length γ.val.val)) hb
    simpa only [Real.coe_toNNReal _ (H.length_pos γ.val.val).le] using hh
  · have hh := ((mem_mixedCurveWindowCatalog T X L color _ γ.val).mp γ.property).2.2
    simpa only [one_mul] using (physicalLength_mem_image γ.val B.carrier).mp hh

lemma colored_factorial_moment_eq_catalog_card {ι : Type*} [Fintype ι] (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (color : ι→Bool)
    (B : ι→WP.Probability.RelCompactBorelWindow ℝ≥0) (a : ι→ℕ)
    (hBL : ∀i b,b∈(B i).carrier → (b:ℝ)≤L)
    (hB : ∀i j,i≠j → color i=color j → Disjoint (B i).carrier (B j).carrier) :
    (∏i,((coloredLengthPointMeasure T X (color i)).count ℝ≥0 (B i)).descFactorial (a i))=
      Nat.card (CatalogTuple (fun i => mixedCurveWindowCatalog T X L (color i) (NNReal.toReal '' (B i).carrier)) a) := by
  simp_rw [coloredLengthPointMeasure_count_eq_catalog T X _ _ L (hBL _)]
  symm
  apply catalogTuple_card
  apply mixedCurveWindowCatalog_disjoint T hg
  intro i j hij hc
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hax⟩ ⟨b,hb,hbx⟩
  have hab : a=b := NNReal.coe_injective (hax.trans hbx.symm)
  subst b
  exact Set.disjoint_left.mp (hB i j hij hc) ha hb
end WP.Critical
