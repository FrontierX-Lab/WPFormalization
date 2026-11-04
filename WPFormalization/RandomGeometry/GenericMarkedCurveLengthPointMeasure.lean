import WPFormalization.RandomGeometry.CurveLengthPointMeasures

/-! Genuine marked counting measures on scaled primitive lengths and a discrete
natural mark. The pre-existing complete short-curve catalogue proves finiteness
using only the length projection, even for windows containing arbitrary marks.
All rectangles retain the same curve predicate and multiplicities. No geometric
moment, asymptotic law or new classical measurability criterion is assumed. -/

noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def genericMarkedCurveLengthMeasure (X : G.Moduli g n (fun _ => 0)) (s : ℝ)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ) :
    Measure (ℝ≥0 × ℕ) :=
  Measure.sum (fun γ : {γ : H.Primitive g n X // p γ} =>
    Measure.dirac (Real.toNNReal (s * H.length γ.val), mark γ.val))

lemma genericMarkedCurveLengthMeasure_finite_window
    (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (hs : 0 < s)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ)
    (B : Set (ℝ≥0 × ℕ)) (hB : BddAbove (Prod.fst '' B)) :
    Finite {γ : {γ : H.Primitive g n X // p γ} //
      (Real.toNNReal (s * H.length γ.val), mark γ.val) ∈ B} := by
  rcases hB with ⟨U,hU⟩
  letI := curveNNLengthMeasure_finite_below H X s hs p U
  let f : {γ : {γ : H.Primitive g n X // p γ} //
      (Real.toNNReal (s * H.length γ.val), mark γ.val) ∈ B} →
      {γ : {γ : H.Primitive g n X // p γ} //
        Real.toNNReal (s * H.length γ.val) ≤ U} :=
    fun γ => ⟨γ.val,hU ⟨_,γ.property,rfl⟩⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    change a.val=b.val at hh
    exact hh)

lemma genericMarkedCurveLengthMeasure_isLocallyFinite
    (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (hs : 0 < s)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ) :
    IsLocallyFiniteMeasure (genericMarkedCurveLengthMeasure H X s p mark) := by
  constructor
  intro x
  let B : Set (ℝ≥0 × ℕ) := Iic (x.1+1) ×ˢ univ
  have hB : BddAbove (Prod.fst '' B) := by
    refine ⟨x.1+1,?_⟩
    rintro t ⟨y,hy,rfl⟩
    exact hy.1
  letI := genericMarkedCurveLengthMeasure_finite_window H X s hs p mark B hB
  refine ⟨B,prod_mem_nhds (Iic_mem_nhds (by simp)) univ_mem,?_⟩
  change genericMarkedCurveLengthMeasure H X s p mark B < ∞
  rw [genericMarkedCurveLengthMeasure,
    sum_dirac_apply_eq_natCard _ B (measurableSet_Iic.prod MeasurableSet.univ)]
  exact ENNReal.natCast_lt_top _

lemma genericMarkedCurveLengthMeasure_integerOnRelCompact
    (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (hs : 0 < s)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ)
    (B : Set (ℝ≥0 × ℕ)) (hB : MeasurableSet B) (hcomp : IsCompact (closure B)) :
    ∃ N : ℕ, genericMarkedCurveLengthMeasure H X s p mark B=(N : ℝ≥0∞) := by
  have hbdd : BddAbove (Prod.fst '' B) :=
    (hcomp.image continuous_fst).bddAbove.mono (Set.image_mono subset_closure)
  letI := genericMarkedCurveLengthMeasure_finite_window H X s hs p mark B hbdd
  exact ⟨_,sum_dirac_apply_eq_natCard _ B hB⟩

def genericMarkedCurveLengthPointMeasure
    (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (hs : 0 < s)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ) :
    WP.Probability.PointMeasure (ℝ≥0 × ℕ) where
  toMeasure := genericMarkedCurveLengthMeasure H X s p mark
  locallyFinite := genericMarkedCurveLengthMeasure_isLocallyFinite H X s hs p mark
  regular := by
    letI := genericMarkedCurveLengthMeasure_isLocallyFinite H X s hs p mark
    infer_instance
  integerOnRelCompact := genericMarkedCurveLengthMeasure_integerOnRelCompact H X s hs p mark

lemma genericMarkedCurveLengthMeasure_rectangle
    (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (hs : 0 < s)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ)
    (B : Set ℝ≥0) (hB : MeasurableSet B) (hbounded : BddAbove B) (k : ℕ) :
    genericMarkedCurveLengthMeasure H X s p mark (B ×ˢ {k}) =
      (Nat.card {γ : H.Primitive g n X //
        p γ ∧ Real.toNNReal (s * H.length γ) ∈ B ∧ mark γ=k} : ℝ≥0∞) := by
  have hbdd : BddAbove (Prod.fst '' (B ×ˢ ({k} : Set ℕ))) := by
    apply hbounded.mono
    rintro t ⟨y,hy,rfl⟩
    exact hy.1
  letI := genericMarkedCurveLengthMeasure_finite_window H X s hs p mark _ hbdd
  rw [genericMarkedCurveLengthMeasure,
    sum_dirac_apply_eq_natCard _ _ (hB.prod (measurableSet_singleton k))]
  congr 1
  apply Nat.card_congr
  exact {
    toFun := fun γ => ⟨γ.val.val,γ.val.property,γ.property.1,γ.property.2⟩
    invFun := fun γ => ⟨⟨γ.val,γ.property.1⟩,γ.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma genericMarkedCurveLengthMeasure_rectangle_eq_filtered
    (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (hs : 0 < s)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ)
    (B : Set ℝ≥0) (hB : MeasurableSet B) (hbounded : BddAbove B) (k : ℕ) :
    genericMarkedCurveLengthMeasure H X s p mark (B ×ˢ {k}) =
      (curveLengthPointMeasure H X s hs (fun γ => p γ ∧ mark γ=k)).toMeasure B := by
  rw [genericMarkedCurveLengthMeasure_rectangle H X s hs p mark B hB hbounded k]
  change _=curveNNLengthMeasure H X s _ B
  letI := curveNNLengthMeasure_finite_window H X s hs (fun γ => p γ ∧ mark γ=k) B hbounded
  rw [curveNNLengthMeasure,sum_dirac_apply_eq_natCard _ B hB]
  congr 1
  apply Nat.card_congr
  exact {
    toFun := fun γ => ⟨⟨γ.val,γ.property.1,γ.property.2.2⟩,γ.property.2.1⟩
    invFun := fun γ => ⟨γ.val.val,γ.val.property.1,γ.property,γ.val.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end WP.RandomGeometry

namespace WP.Probability
open MeasureTheory Set
open scoped NNReal

def markedRectangleWindow (B : RelCompactBorelWindow ℝ≥0) (k : ℕ) :
    RelCompactBorelWindow (ℝ≥0 × ℕ) where
  carrier := B.carrier ×ˢ {k}
  measurableSet := B.measurableSet.prod (measurableSet_singleton k)
  compactClosure := by
    rw [closure_prod_eq,closure_singleton]
    exact B.compactClosure.prod isCompact_singleton

end WP.Probability

namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

lemma genericMarkedCurveLengthPointMeasure_rectangle_count
    (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (hs : 0 < s)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ)
    (B : RelCompactBorelWindow ℝ≥0) (k : ℕ) :
    (genericMarkedCurveLengthPointMeasure H X s hs p mark).count (ℝ≥0 × ℕ)
      (markedRectangleWindow B k) =
      Nat.card {γ : H.Primitive g n X //
        p γ ∧ Real.toNNReal (s * H.length γ) ∈ B.carrier ∧ mark γ=k} := by
  have hm := genericMarkedCurveLengthMeasure_rectangle H X s hs p mark
    B.carrier B.measurableSet (B.compactClosure.bddAbove.mono subset_closure) k
  change (genericMarkedCurveLengthPointMeasure H X s hs p mark).toMeasure
    (markedRectangleWindow B k).carrier = _ at hm
  rw [(genericMarkedCurveLengthPointMeasure H X s hs p mark).count_spec
    (ℝ≥0 × ℕ) (markedRectangleWindow B k)] at hm
  exact_mod_cast hm

lemma genericMarkedCurveLengthPointMeasure_rectangle_count_eq_filtered
    (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (hs : 0 < s)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ)
    (B : RelCompactBorelWindow ℝ≥0) (k : ℕ) :
    (genericMarkedCurveLengthPointMeasure H X s hs p mark).count (ℝ≥0 × ℕ)
      (markedRectangleWindow B k) =
      (curveLengthPointMeasure H X s hs (fun γ => p γ ∧ mark γ=k)).count ℝ≥0 B := by
  have hm := genericMarkedCurveLengthMeasure_rectangle_eq_filtered H X s hs p mark
    B.carrier B.measurableSet (B.compactClosure.bddAbove.mono subset_closure) k
  change (genericMarkedCurveLengthPointMeasure H X s hs p mark).toMeasure
    (markedRectangleWindow B k).carrier = _ at hm
  rw [(genericMarkedCurveLengthPointMeasure H X s hs p mark).count_spec
    (ℝ≥0 × ℕ) (markedRectangleWindow B k)] at hm
  rw [(curveLengthPointMeasure H X s hs (fun γ => p γ ∧ mark γ=k)).count_spec ℝ≥0 B] at hm
  exact_mod_cast hm

@[simp] lemma genericMarkedCurveLengthPointMeasure_toMeasure
    (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (hs : 0 < s)
    (p : H.Primitive g n X → Prop) (mark : H.Primitive g n X → ℕ) :
    (genericMarkedCurveLengthPointMeasure H X s hs p mark).toMeasure =
      genericMarkedCurveLengthMeasure H X s p mark := rfl

/-- Transfer an already established scalar count measurability statement to the
actual marked rectangle count. An arbitrary predicate or mark is not asserted
measurable without a hypothesis. -/
lemma genericMarkedCurveLengthPointMeasure_rectangle_measurable
    (s : ℝ) (hs : 0 < s)
    (p : (X : G.Moduli g n (fun _ => 0)) → H.Primitive g n X → Prop)
    (mark : (X : G.Moduli g n (fun _ => 0)) → H.Primitive g n X → ℕ)
    (B : RelCompactBorelWindow ℝ≥0) (k : ℕ)
    (hfiltered : Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (curveLengthPointMeasure H X s hs (fun γ => p X γ ∧ mark X γ=k)).count ℝ≥0 B)) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (genericMarkedCurveLengthPointMeasure H X s hs (p X) (mark X)).count
        (ℝ≥0 × ℕ) (markedRectangleWindow B k)) := by
  simpa only [genericMarkedCurveLengthPointMeasure_rectangle_count_eq_filtered] using hfiltered

lemma genericMarkedCurveLengthPointMeasure_rectangle_aemeasurable
    (μ : Measure (G.Moduli g n (fun _ => 0))) (s : ℝ) (hs : 0 < s)
    (p : (X : G.Moduli g n (fun _ => 0)) → H.Primitive g n X → Prop)
    (mark : (X : G.Moduli g n (fun _ => 0)) → H.Primitive g n X → ℕ)
    (B : RelCompactBorelWindow ℝ≥0) (k : ℕ)
    (hfiltered : AEMeasurable (fun X : G.Moduli g n (fun _ => 0) =>
      (curveLengthPointMeasure H X s hs (fun γ => p X γ ∧ mark X γ=k)).count ℝ≥0 B) μ) :
    AEMeasurable (fun X : G.Moduli g n (fun _ => 0) =>
      (genericMarkedCurveLengthPointMeasure H X s hs (p X) (mark X)).count
        (ℝ≥0 × ℕ) (markedRectangleWindow B k)) μ := by
  simpa only [genericMarkedCurveLengthPointMeasure_rectangle_count_eq_filtered] using hfiltered

end WP.RandomGeometry
