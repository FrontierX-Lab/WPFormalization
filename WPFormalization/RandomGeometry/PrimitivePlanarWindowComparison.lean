import WPFormalization.RandomGeometry.GeneralPlanarLengthProjectionCounts

/-! Actual primitive and planar window counts agree whenever the bounded
physical window contains no nonplanar primitive. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

lemma curveLengthPointMeasure_count_eq_of_predicate_on_window (X : G.Moduli g n (fun _=>0))
    (s : ℝ) (hs : 0<s) (p q : H.Primitive g n X→Prop) (B : RelCompactBorelWindow ℝ≥0)
    (h : ∀γ,Real.toNNReal (s*H.length γ)∈B.carrier→(p γ↔q γ)) :
    (curveLengthPointMeasure H X s hs p).count ℝ≥0 B=(curveLengthPointMeasure H X s hs q).count ℝ≥0 B := by
  rw [curveLengthPointMeasure_count_eq_natCard,curveLengthPointMeasure_count_eq_natCard]
  apply Nat.card_congr
  exact {
    toFun:=fun γ=>⟨⟨γ.val.val,(h γ.val.val γ.property).mp γ.val.property⟩,γ.property⟩
    invFun:=fun γ=>⟨⟨γ.val.val,(h γ.val.val γ.property).mpr γ.val.property⟩,γ.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }

lemma primitiveLengthPointProcess_prefix_count_measurable (b : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (primitiveLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow b)) := by
  simp_rw [primitiveLengthPointProcess,primitiveLengthPointMeasure_prefix_count]
  exact H.measurable_primitiveCount g n _

lemma primitiveLengthPointProcess_Ioc_count_measurable (a b : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (primitiveLengthPointProcess H X).count ℝ≥0 (lengthIocWindow a b)) := by
  change Measurable (fun X : G.Moduli g n (fun _=>0)=>
    (primitiveLengthPointProcess H X).count ℝ≥0 (nnrealIocWindow a b))
  simp_rw [PointMeasure.count_nnrealIoc]
  exact (primitiveLengthPointProcess_prefix_count_measurable H b).sub
    (primitiveLengthPointProcess_prefix_count_measurable H a)

lemma primitiveLengthPointProcess_rational_count_measurable (a b : ℚ) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (primitiveLengthPointProcess H X).count ℝ≥0 (nnrealRationalWindow a b)) := by
  simp_rw [pointMeasure_count_rational_window_eq_canonical_Ioc _
    (primitiveLengthPointProcess_singleton_zero H _) a b]
  exact primitiveLengthPointProcess_Ioc_count_measurable H _ _

lemma primitive_planar_Ioc_window_count_eq (X : G.Moduli g n (fun _=>0)) (a b : ℝ≥0)
    (h : ∀γ : H.Primitive g n X,H.length γ≤(b:ℝ)/pantsLengthScale g n→H.planarSide γ≠none) :
    (primitiveLengthPointProcess H X).count ℝ≥0 (lengthIocWindow a b)=
      (generalPlanarLengthPointProcess H X).count ℝ≥0 (lengthIocWindow a b) := by
  apply curveLengthPointMeasure_count_eq_of_predicate_on_window H X _ (pantsLengthScale_pos g n)
    (fun _=>True) (IsPlanarPrimitive H) (lengthIocWindow a b)
  intro γ hγ
  have hh := (scaled_length_mem_Ioc (pantsLengthScale g n) (pantsLengthScale_pos g n) a b _).mp hγ
  have hn := h γ hh.2
  constructor
  · intro _
    cases he : H.planarSide γ with
    | none => exact (hn he).elim
    | some S => exact ⟨S,he⟩
  · intro _
    trivial

end WP.RandomGeometry
