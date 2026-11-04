import WPFormalization.RandomGeometry.PrimitiveSystolicPlanarity
import WPFormalization.RandomGeometry.GeneralPlanarMarkedPrefixFiniteness

/-! Actual minimum-curve selections and their atoms in the genuine marked
process. The specification allows arbitrary ties between shortest curves. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def IsSystolicTypeSelection (X : G.Moduli g n (fun _=>0)) (k : ℕ) : Prop :=
  (∃γ : H.Primitive g n X,IsSystolicPrimitive H γ ∧k=planarPrimitiveCuspType H γ) ∨
    (IsEmpty (H.Primitive g n X) ∧k=0)

lemma generalPlanarMarkedLengthPointProcess_atom_of_planar
    (X : G.Moduli g n (fun _=>0)) (γ : H.Primitive g n X) (hp : IsPlanarPrimitive H γ) :
    (generalPlanarMarkedLengthPointProcess H X).toMeasure
      {(Real.toNNReal (pantsLengthScale g n*H.length γ),planarPrimitiveCuspType H γ)}≠0 := by
  let a : {γ : H.Primitive g n X //IsPlanarPrimitive H γ} := ⟨γ,hp⟩
  change genericMarkedCurveLengthMeasure H X _ _ _ _≠0
  rw [genericMarkedCurveLengthMeasure,Measure.sum_apply _ (measurableSet_singleton _)]
  have hh := ENNReal.le_tsum (f:=fun δ : {γ : H.Primitive g n X //IsPlanarPrimitive H γ}=>
    (Measure.dirac (Real.toNNReal (pantsLengthScale g n*H.length δ.val),planarPrimitiveCuspType H δ.val))
      {(Real.toNNReal (pantsLengthScale g n*H.length γ),planarPrimitiveCuspType H γ)}) a
  have h1 := hh
  simp only [a,Measure.dirac_apply_of_mem (mem_singleton _)] at h1
  exact ne_of_gt (zero_lt_one.trans_le h1)

lemma generalPlanarMarkedLengthPointProcess_before_systolic_eq_zero
    (X : G.Moduli g n (fun _=>0)) (γ : H.Primitive g n X) (hγ : IsSystolicPrimitive H γ) :
    (generalPlanarMarkedLengthPointProcess H X).toMeasure
      (Iio (Real.toNNReal (pantsLengthScale g n*H.length γ))×ˢ(univ : Set ℕ))=0 := by
  change genericMarkedCurveLengthMeasure H X _ _ _ _=0
  rw [genericMarkedCurveLengthMeasure,Measure.sum_apply _ (measurableSet_Iio.prod MeasurableSet.univ)]
  apply ENNReal.tsum_eq_zero.mpr
  intro δ
  have hmin : H.length γ≤H.length δ.val := by
    apply (ENNReal.ofReal_le_ofReal_iff (H.length_pos δ.val).le).mp
    change ENNReal.ofReal (H.length γ)=primitiveMinimumLength H X at hγ
    rw [hγ]
    exact iInf_le _ δ.val
  have hnot : (Real.toNNReal (pantsLengthScale g n*H.length δ.val),planarPrimitiveCuspType H δ.val)∉
      Iio (Real.toNNReal (pantsLengthScale g n*H.length γ))×ˢ(univ : Set ℕ) := by
    intro hh
    have hle := Real.toNNReal_mono (mul_le_mul_of_nonneg_left hmin (pantsLengthScale_pos g n).le)
    exact not_lt_of_ge hle hh.1
  simp only [Measure.dirac_apply,indicator_of_notMem hnot]

lemma primitiveMinimumLength_eq_top_of_isEmpty (X : G.Moduli g n (fun _=>0))
    (h : IsEmpty (H.Primitive g n X)) : primitiveMinimumLength H X=∞ := by
  letI := h
  simp [primitiveMinimumLength]

lemma generalPlanarMarkedLengthPointProcess_eq_zero_of_isEmpty (X : G.Moduli g n (fun _=>0))
    (h : IsEmpty (H.Primitive g n X)) : (generalPlanarMarkedLengthPointProcess H X).toMeasure=0 := by
  letI := h
  change genericMarkedCurveLengthMeasure H X _ _ _=0
  simp [genericMarkedCurveLengthMeasure]

lemma primitive_systolic_scaled_length_eq (X : G.Moduli g n (fun _=>0))
    (γ : H.Primitive g n X) (hγ : IsSystolicPrimitive H γ) :
    ENNReal.ofReal (pantsLengthScale g n)*primitiveMinimumLength H X=
      ENNReal.ofReal (pantsLengthScale g n*H.length γ) := by
  change ENNReal.ofReal (H.length γ)=primitiveMinimumLength H X at hγ
  rw [←hγ,ENNReal.ofReal_mul (pantsLengthScale_pos g n).le]

end WP.RandomGeometry
