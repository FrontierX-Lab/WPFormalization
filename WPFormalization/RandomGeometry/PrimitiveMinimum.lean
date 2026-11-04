import WPFormalization.RandomGeometry.PantsMinimum
import WPFormalization.RandomGeometry.PrimitivePlanarWindowComparison

/-! The actual shortest unoriented primitive length, with infinity for an
empty catalog. Local finiteness gives the exact strict-tail/void equivalence. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def primitiveMinimumLength (X : G.Moduli g n (fun _=>0)) : ℝ≥0∞ :=
  ⨅γ : H.Primitive g n X,ENNReal.ofReal (H.length γ)

lemma primitiveMinimumLength_scaled (X : G.Moduli g n (fun _=>0)) (s : ℝ) (hs : 0<s) :
    ENNReal.ofReal s*primitiveMinimumLength H X=⨅γ : H.Primitive g n X,ENNReal.ofReal (s*H.length γ) := by
  rw [primitiveMinimumLength,ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hs) ENNReal.ofReal_ne_top]
  congr 1
  funext γ
  exact (ENNReal.ofReal_mul hs.le).symm

lemma primitiveMinimumLength_gt_iff_prefix_count_zero (X : G.Moduli g n (fun _=>0))
    (s : ℝ) (hs : 0<s) (t : ℝ≥0) :
    (t:ℝ≥0∞)<ENNReal.ofReal s*primitiveMinimumLength H X ↔
      (primitiveLengthPointMeasure H X s hs).count ℝ≥0 (nnrealPrefixWindow t)=0 := by
  let f := fun γ : H.Primitive g n X=>s*H.length γ
  let A := {γ : H.Primitive g n X //f γ≤(t:ℝ)+1}
  let ff : A→{γ : H.Primitive g n X //γ∈H.shortPrimitive X (((t:ℝ)+1)/s)} :=
    fun γ=>⟨γ.val,(H.mem_shortPrimitive X _ _).mpr ((le_div_iff₀ hs).mpr (by simpa [f,mul_comm] using γ.property))⟩
  haveI : Finite A := Finite.of_injective ff (by intro a b he;apply Subtype.ext;exact congrArg (fun z : {γ : H.Primitive g n X //γ∈H.shortPrimitive X (((t:ℝ)+1)/s)}=>z.val) he)
  rw [primitiveMinimumLength_scaled H X s hs,←ENNReal.ofReal_coe_nnreal]
  rw [ofReal_lt_iInf_iff_of_finite_below (fun γ : H.Primitive g n X=>s*H.length γ) (t:ℝ) t.property]
  rw [primitiveLengthPointMeasure_prefix_count,H.primitiveCount_eq_card]
  constructor
  · intro hall
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro γ hγ
    have hl := (le_div_iff₀ hs).mp ((H.mem_shortPrimitive X _ γ).mp hγ)
    exact (not_lt_of_ge (by simpa [mul_comm] using hl)) (hall γ)
  · intro hzero γ
    by_contra hγ
    have hmem := (H.mem_shortPrimitive X ((t:ℝ)/s) γ).mpr
      ((le_div_iff₀ hs).mpr (by simpa [mul_comm] using le_of_not_gt hγ))
    have hpos := Finset.card_pos.mpr ⟨γ,hmem⟩
    omega

lemma primitiveLengthPointProcess_prefix_count_eq_minimum_void (X : G.Moduli g n (fun _=>0))
    (t : ℝ≥0) :
    (primitiveLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow t)=0 ↔
      (t:ℝ≥0∞)<ENNReal.ofReal (pantsLengthScale g n)*primitiveMinimumLength H X :=
  (primitiveMinimumLength_gt_iff_prefix_count_zero H X _ (pantsLengthScale_pos g n) t).symm

lemma primitiveMinimumLength_measurable :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>primitiveMinimumLength H X) := by
  apply measurable_of_Ioi
  intro b
  by_cases hb : b=⊤
  · subst b
    simp
  · have hbt : (b.toNNReal:ℝ≥0∞)=b := ENNReal.coe_toNNReal hb
    have he : {X : G.Moduli g n (fun _=>0)|b<primitiveMinimumLength H X}=
        {X |H.primitiveCount X (b.toNNReal:ℝ)=0} := by
      ext X
      rw [←hbt]
      have hh := primitiveMinimumLength_gt_iff_prefix_count_zero H X 1 (by norm_num) b.toNNReal
      simpa only [ENNReal.ofReal_one,one_mul,primitiveLengthPointMeasure_prefix_count,div_one,mem_setOf_eq,ENNReal.toNNReal_coe] using hh
    change MeasurableSet {X : G.Moduli g n (fun _=>0)|b<primitiveMinimumLength H X}
    rw [he]
    exact (measurableSet_singleton 0).preimage (H.measurable_primitiveCount _ _ _)

end WP.RandomGeometry
