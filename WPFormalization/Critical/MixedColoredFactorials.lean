import WPFormalization.Critical.MixedCurveCatalogs
import WPFormalization.Critical.MixedColoredSlots
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory Finset Set
open scoped Classical ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    {g n : ℕ}

lemma mixedCurveTypes_coloredSlots_iff {ι : Type*} [Fintype ι]
    (a : ι→ℕ) (color : ι→Bool) (X : G.Moduli g n (fun _ => 0))
    (γ : Fin (pantsSlotsCount a color+nonsepSlotsCount a color) → H.Primitive g n X) :
    MixedCurveTypes T γ ↔ ∀s : ColoredSlots a,ColoredCurveType T (color s.1) (γ (coloredSlotsEquiv a color s)) := by
  constructor
  · intro h s
    have hh (j : Fin (pantsSlotsCount a color+nonsepSlotsCount a color)) :
        ColoredCurveType T (color ((coloredSlotsEquiv a color).symm j).1) (γ j) := by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [coloredSlotsEquiv_pants a color i]
        exact h.1 i
      · rw [coloredSlotsEquiv_nonsep a color i]
        exact h.2 i
    simpa only [Equiv.symm_apply_apply] using hh (coloredSlotsEquiv a color s)
  · intro h
    constructor
    · intro i
      have hh := h ((coloredSlotsEquiv a color).symm (i.castAdd (nonsepSlotsCount a color)))
      rw [Equiv.apply_symm_apply,coloredSlotsEquiv_pants a color i] at hh
      exact hh
    · intro i
      have hh := h ((coloredSlotsEquiv a color).symm (Fin.natAdd (pantsSlotsCount a color) i))
      rw [Equiv.apply_symm_apply,coloredSlotsEquiv_nonsep a color i] at hh
      exact hh

def coloredCatalogMixedTupleEquiv {ι : Type*} [Fintype ι]
    (a : ι→ℕ) (color : ι→Bool) (X : G.Moduli g n (fun _ => 0))
    (L : ℝ) (I : ι→Set ℝ) (hIL : ∀i,I i⊆Icc 0 L) :
    CatalogTuple (fun i => mixedCurveWindowCatalog T X L (color i) (I i)) a ≃
      MixedWindowTuple T X (fun j => I ((coloredSlotsEquiv a color).symm j).1) where
  toFun t := ⟨fun j => t.val ((coloredSlotsEquiv a color).symm j),
    t.property.1.comp (coloredSlotsEquiv a color).symm.injective,
    (mixedCurveTypes_coloredSlots_iff T a color X _).mpr (by
      intro s
      simpa only [Equiv.symm_apply_apply] using
        ((mem_mixedCurveWindowCatalog T X L (color s.1) (I s.1) (t.val s)).mp (t.property.2 s)).2.1),
    fun j => ((mem_mixedCurveWindowCatalog T X L _ _ _).mp (t.property.2 ((coloredSlotsEquiv a color).symm j))).2.2⟩
  invFun t := ⟨fun s => t.val (coloredSlotsEquiv a color s),
    t.property.1.comp (coloredSlotsEquiv a color).injective,by
      intro s
      apply (mem_mixedCurveWindowCatalog T X L (color s.1) (I s.1) _).mpr
      have hw : H.length (t.val (coloredSlotsEquiv a color s))∈I s.1 := by
        simpa only [Equiv.symm_apply_apply] using t.property.2.2 (coloredSlotsEquiv a color s)
      exact ⟨(hIL s.1 hw).2,(mixedCurveTypes_coloredSlots_iff T a color X t.val).mp t.property.2.1 s,hw⟩⟩
  left_inv t := by
    apply Subtype.ext
    funext s
    exact congrArg t.val ((coloredSlotsEquiv a color).symm_apply_apply s)
  right_inv t := by
    apply Subtype.ext
    funext j
    exact congrArg t.val ((coloredSlotsEquiv a color).apply_symm_apply j)

lemma catalogTuple_finite {ι α : Type*} [Fintype ι] (F : ι→Finset α) (a : ι→ℕ) :
    Finite (CatalogTuple F a) := by
  let f : CatalogTuple F a → (∀i,Fin (a i)→{x // x∈F i}) := fun t i j => ⟨t.val ⟨i,j⟩,t.property.2 ⟨i,j⟩⟩
  apply Finite.of_injective f
  intro t s h
  apply Subtype.ext
  funext j
  exact congrArg (fun v => (v j.1 j.2).val) h

lemma colored_factorial_eq_actual_mixed_tuple_count {ι : Type*} [Fintype ι] (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (color : ι→Bool)
    (B : ι→WP.Probability.RelCompactBorelWindow ℝ≥0) (a : ι→ℕ)
    (hBL : ∀i b,b∈(B i).carrier → (b:ℝ)≤L)
    (hB : ∀i j,i≠j → color i=color j → Disjoint (B i).carrier (B j).carrier) :
    (∏i,(((coloredLengthPointMeasure T X (color i)).count ℝ≥0 (B i)).descFactorial (a i) : ℝ≥0∞))=
      mixedWindowTupleCount T X (fun j => NNReal.toReal '' (B ((coloredSlotsEquiv a color).symm j).1).carrier) := by
  rw [←Nat.cast_prod,colored_factorial_moment_eq_catalog_card T hg X L color B a hBL hB]
  let F := fun i => mixedCurveWindowCatalog T X L (color i) (NNReal.toReal '' (B i).carrier)
  letI : Finite (CatalogTuple F a) := catalogTuple_finite F a
  letI := Fintype.ofFinite (CatalogTuple F a)
  have hi (i : ι) : NNReal.toReal '' (B i).carrier ⊆ Icc 0 L := by
    rintro _ ⟨b,hb,rfl⟩
    exact ⟨b.2,hBL i b hb⟩
  calc
    _ = ∑' _ : CatalogTuple F a,(1 : ℝ≥0∞) := by
      change (Nat.card (CatalogTuple F a) : ℝ≥0∞)=_
      rw [tsum_fintype]
      simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.card_eq_fintype_card]
    _ = _ := (coloredCatalogMixedTupleEquiv T a color X L _ hi).tsum_eq (fun _ => (1 : ℝ≥0∞))
lemma coloredSlots_intensity_product {ι M : Type*} [Fintype ι] [CommMonoid M]
    (a : ι→ℕ) (color : ι→Bool) (pants nonsep : ι→M) :
    ((∏j : Fin (pantsSlotsCount a color),pants ((coloredSlotsEquiv a color).symm
      (j.castAdd (nonsepSlotsCount a color))).1)*
      ∏i : Fin (nonsepSlotsCount a color),nonsep ((coloredSlotsEquiv a color).symm
      (Fin.natAdd (pantsSlotsCount a color) i)).1)=
      ∏i,(if color i then pants i else nonsep i)^(a i) := by
  have he := mixedSlots_prod a _ (coloredSlotsEquiv a color) (fun i => if color i then pants i else nonsep i)
  rw [Fin.prod_univ_add] at he
  simpa only [coloredSlotsEquiv_pants a color,coloredSlotsEquiv_nonsep a color,
    ite_true,Bool.false_eq_true,ite_false] using he
end WP.Critical
