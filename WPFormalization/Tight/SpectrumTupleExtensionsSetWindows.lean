import WPFormalization.Tight.SpectrumTupleExtensionsPointProcess
/- Appendix F.4: arbitrary Borel-window tuple identification and exact
connected/separating orbit split, all on the original actual geometry.
These are finite count proofs, with no moment or limit hypothesis. -/
import WPFormalization.Tight.SpectrumTupleExtensionsOrbitSum
noncomputable section
universe u v w z
namespace WP.Tight.SpectrumTupleExtensions
open External Set
open scoped ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H) {g n : ℕ}
  (X : TightSurface G g 0 n (fun _=>0) (fun _=>0))

def GoodSetTuple {r : ℕ} (W : Fin r → Set ℝ) (Γ : Fin r → Curve Q X) : Prop :=
  Q.GoodTuple Γ ∧ ∀ i, Q.length (Γ i) ∈ W i

def TightSetTuple {r : ℕ} (W : Fin r → Set ℝ) (Γ : Fin r → Curve Q X) : Prop :=
  Function.Injective Γ ∧ ∀ i, Q.primitive (Γ i) ∧ Q.IsTight (Γ i) ∧ Q.length (Γ i) ∈ W i

def ActualTightSetTuple {r : ℕ} (W : Fin r → Set ℝ)
    (Γ : Fin r → H.Primitive g n (tightCuspSurface G X)) : Prop :=
  Function.Injective Γ ∧ ∀ i, Q.cuspTight X (Γ i) ∧ H.length (Γ i) ∈ W i

lemma goodSetTuple_iff_tightSetTuple_of_not_bad {r : ℕ}
    (W : Fin r → Set ℝ) (b : ℝ) (hb : ∀ i, ∀ l∈W i, l≤b)
    (hnobad : ¬BadConfiguration Q X b) (Γ : Fin r → Curve Q X) :
    GoodSetTuple Q X W Γ ↔ TightSetTuple Q X W Γ := by
  constructor
  · rintro ⟨hgood,hw⟩
    exact ⟨hgood.1,fun i=>⟨(hgood.2.1 i).1,(hgood.2.1 i).2.1,hw i⟩⟩
  · rintro ⟨hinj,ht⟩
    refine ⟨⟨hinj,?_,?_⟩,fun i=>(ht i).2.2⟩
    · intro i
      refine ⟨(ht i).1,(ht i).2.1,?_,?_⟩
      · by_contra hnot
        exact hnobad (Or.inl ⟨Γ i,(ht i).1,(ht i).2.1,hb i _ (ht i).2.2,hnot⟩)
      · exact ⟨(ht i).2.1.1,fun j=>Fin.elim0 j⟩
    · intro i j hij
      by_contra hnot
      exact hnobad (Or.inr ⟨Γ i,Γ j,fun heq=>hij (hinj heq),(ht i).1,(ht j).1,
        (ht i).2.1,(ht j).2.1,hb i _ (ht i).2.2,hb j _ (ht j).2.2,hnot⟩)

def tightSetTupleEquivActual {r : ℕ} (W : Fin r → Set ℝ) :
    {Γ : Fin r → Curve Q X // TightSetTuple Q X W Γ} ≃
    {Γ : Fin r → H.Primitive g n (tightCuspSurface G X) // ActualTightSetTuple Q X W Γ} where
  toFun Γ := ⟨fun i=>Q.cuspPrimitiveEquiv g n X ⟨Γ.val i,(Γ.property.2 i).1⟩,by
    refine ⟨?_,?_⟩
    · intro i j h
      exact Γ.property.1 (congrArg Subtype.val ((Q.cuspPrimitiveEquiv g n X).injective h))
    · intro i
      refine ⟨?_,?_⟩
      · simpa only [TightGeodesicGeometry.cuspTight,Equiv.symm_apply_apply] using (Γ.property.2 i).2.1
      · simpa only [Q.cuspPrimitive_length] using (Γ.property.2 i).2.2⟩
  invFun Γ := ⟨fun i=>((Q.cuspPrimitiveEquiv g n X).symm (Γ.val i)).val,by
    refine ⟨?_,?_⟩
    · intro i j h
      apply Γ.property.1
      apply (Q.cuspPrimitiveEquiv g n X).symm.injective
      exact Subtype.ext h
    · intro i
      refine ⟨((Q.cuspPrimitiveEquiv g n X).symm (Γ.val i)).property,(Γ.property.2 i).1,?_⟩
      have hl := Q.cuspPrimitive_length g n X ((Q.cuspPrimitiveEquiv g n X).symm (Γ.val i))
      rw [Equiv.apply_symm_apply] at hl
      rw [←hl]
      exact (Γ.property.2 i).2⟩
  left_inv Γ := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((Q.cuspPrimitiveEquiv g n X).symm_apply_apply _)
  right_inv Γ := by
    apply Subtype.ext
    funext i
    exact (Q.cuspPrimitiveEquiv g n X).apply_symm_apply (Γ.val i)

theorem actual_set_count_eq_good_set_count_of_not_bad {r : ℕ}
    (W : Fin r → Set ℝ) (b : ℝ) (hb : ∀ i, ∀ l∈W i, l≤b)
    (hnobad : ¬BadConfiguration Q X b) :
    Nat.card {Γ : Fin r → H.Primitive g n (tightCuspSurface G X) // ActualTightSetTuple Q X W Γ} =
    Nat.card {Γ : Fin r → Curve Q X // GoodSetTuple Q X W Γ} := by
  rw [←Nat.card_congr (tightSetTupleEquivActual Q X W)]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun Γ =>
    (goodSetTuple_iff_tightSetTuple_of_not_bad Q X W b hb hnobad Γ).symm)

lemma good_set_tuple_finite {r : ℕ} (W : Fin r → Set ℝ) (b : ℝ)
    (hb : ∀ i, ∀ l∈W i, l≤b) :
    Finite {Γ : Fin r → Curve Q X // GoodSetTuple Q X W Γ} := by
  letI := finite_primitive_bounded_tuples Q X r b
  apply Finite.of_injective (fun Γ : {Γ : Fin r → Curve Q X // GoodSetTuple Q X W Γ} =>
    (⟨Γ.val,fun i=>⟨(Γ.property.1.2.1 i).1,hb i _ (Γ.property.2 i)⟩⟩ :
      {Γ : Fin r → Curve Q X // ∀i,Q.primitive (Γ i) ∧ Q.length (Γ i)≤b}))
  intro a b h
  exact Subtype.ext (Subtype.mk.inj h)

lemma good_set_count_eq_orbit_sum {r : ℕ}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (W : Fin r → Set ℝ) (b : ℝ) (hb : ∀i,∀l∈W i,l≤b) (hs : Stable g 0) :
    (Nat.card {Γ : Fin r → Curve Q X // GoodSetTuple Q X W Γ} : ℝ≥0∞) =
      ∑ o : A.Orbit g 0 r, A.orbitSum o ({x | ∀i,x i∈W i}.indicator (fun _=>1)) X := by
  classical
  have he (Γ : Fin r→Curve Q X) : GoodSetTuple Q X W Γ ↔
      FilteredOrbitWindowTuple Q A X (fun _=>True) {x | ∀i,x i∈W i} Γ := by
    constructor
    · rintro ⟨hg,hw⟩
      obtain ⟨o,ho,_⟩:=A.orbit_partition X Γ hs hg
      exact ⟨hg,⟨o,ho,trivial⟩,hw⟩
    · rintro ⟨hg,_,hw⟩
      exact ⟨hg,hw⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  simpa only [Finset.filter_true] using filtered_window_count_eq_orbit_sum Q A X
    (fun _=>True) {x | ∀i,x i∈W i} b (fun x hx i=>hb i _ (hx i)) hs

lemma cut_components_pos (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    {r : ℕ} (o : A.Orbit g 0 r) : 0<(A.cut o).components := by
  obtain ⟨c,_⟩ := (A.cut_connected o).1
  have hc := c.isLt
  omega

lemma orbit_sum_eq_connected_add_separating
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q) {r : ℕ}
    (F : (Fin r→ℝ)→ℝ≥0∞) :
    (∑o : A.Orbit g 0 r,A.orbitSum o F X) =
      (∑o∈Finset.univ.filter (fun o : A.Orbit g 0 r=>(A.cut o).components=1),A.orbitSum o F X) +
      ∑o∈Finset.univ.filter (fun o : A.Orbit g 0 r=>2≤(A.cut o).components),A.orbitSum o F X := by
  classical
  rw [←Finset.sum_filter_add_sum_filter_not Finset.univ (fun o : A.Orbit g 0 r=>(A.cut o).components=1)
    (fun o=>A.orbitSum o F X)]
  congr 1
  congr 1
  ext o
  have hp:=cut_components_pos Q A o
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  omega

lemma good_set_count_le_connected_add_separating {r : ℕ}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (W : Fin r→Set ℝ) (b : ℝ) (hb : ∀i,∀l∈W i,l≤b) (hs : Stable g 0) :
    (Nat.card {Γ : Fin r→Curve Q X // GoodSetTuple Q X W Γ} : ℝ≥0∞) ≤
      (∑o∈Finset.univ.filter (fun o : A.Orbit g 0 r=>(A.cut o).components=1),
        A.orbitSum o ({x | ∀i,x i∈W i}.indicator (fun _=>1)) X) +
      (Nat.card {Γ : Fin r→Curve Q X // SeparatingTuple Q A X r b Γ} : ℝ≥0∞) := by
  classical
  rw [good_set_count_eq_orbit_sum Q X A W b hb hs,
    orbit_sum_eq_connected_add_separating Q X A,
    separating_count_eq_orbit_sum Q A X r b hs]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro o ho
  unfold TightMulticurveTopology.orbitSum
  apply ENNReal.tsum_le_tsum
  intro Γ
  by_cases hm : A.orbitMem o X Γ
  · simp only [hm,ite_true]
    rw [cutLengthTest_eq_ite Q X r b Γ]
    by_cases hw : ∀i,Q.length (Γ i)∈W i
    · have hb' : ∀i,Q.length (Γ i)≤b := fun i=>hb i _ (hw i)
      simp only [Set.indicator_apply,Set.mem_setOf_eq,hw,hb',ite_true,le_refl]
    · simp only [Set.indicator_apply,Set.mem_setOf_eq,hw,ite_false,zero_le]
  · simp only [hm,ite_false,le_refl]

lemma connected_count_le_good_set_count {r : ℕ}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (W : Fin r→Set ℝ) (b : ℝ) (hb : ∀i,∀l∈W i,l≤b) (hs : Stable g 0) :
    (∑o∈Finset.univ.filter (fun o : A.Orbit g 0 r=>(A.cut o).components=1),
        A.orbitSum o ({x | ∀i,x i∈W i}.indicator (fun _=>1)) X) ≤
      (Nat.card {Γ : Fin r→Curve Q X // GoodSetTuple Q X W Γ} : ℝ≥0∞) := by
  rw [good_set_count_eq_orbit_sum Q X A W b hb hs,
    orbit_sum_eq_connected_add_separating Q X A]
  exact le_self_add

end WP.Tight.SpectrumTupleExtensions
