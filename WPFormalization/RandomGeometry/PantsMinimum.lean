import WPFormalization.RandomGeometry.PantsPoissonProcess
import Mathlib.Data.Finset.Max

/-! The actual shortest pants length, with infinity when the pants catalog is
empty. Local finiteness turns strict minimum-tail events into void events. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

lemma ofReal_lt_iInf_iff_of_finite_below {α : Type*} (f : α → ℝ)
    (t : ℝ) (ht : 0≤t) [Finite {a : α // f a≤t+1}] :
    ENNReal.ofReal t < ⨅a,ENNReal.ofReal (f a) ↔ ∀a,t<f a := by
  classical
  constructor
  · intro h a
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mp (h.trans_le (iInf_le _ a))
  · intro h
    letI : Fintype {a : α // f a≤t+1} := Fintype.ofFinite _
    let S : Finset ℝ := insert (t+1) (Finset.univ.image
      (fun a : {a : α // f a≤t+1} => f a.val))
    have hs : S.Nonempty := ⟨t+1,Finset.mem_insert_self _ _⟩
    let m : ℝ := S.min' hs
    have htm : t < m := by
      apply (Finset.lt_min'_iff S hs).mpr
      intro x hx
      rcases Finset.mem_insert.mp hx with he | hx
      · rw [he]
        linarith
      · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
        exact h a.val
    have hmall (a : α) : m ≤ f a := by
      by_cases ha : f a≤t+1
      · exact S.min'_le _ (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,rfl⟩))
      · exact (S.min'_le _ (Finset.mem_insert_self _ _)).trans (le_of_lt (lt_of_not_ge ha))
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr htm).trans_le
      (le_iInf (fun a => ENNReal.ofReal_le_ofReal (hmall a)))

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def pantsMinimumLength (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ⨅γ : {γ : H.Primitive g n X //
    ∃S : Finset (Fin n), H.planarSide γ=some S ∧ S.card=2},
    ENNReal.ofReal (H.length γ.val)

lemma pantsMinimumLength_scaled (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) :
    ENNReal.ofReal s*pantsMinimumLength H X =
      ⨅γ : {γ : H.Primitive g n X //
        ∃S : Finset (Fin n), H.planarSide γ=some S ∧ S.card=2},
        ENNReal.ofReal (s*H.length γ.val) := by
  rw [pantsMinimumLength,ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hs)
    ENNReal.ofReal_ne_top]
  congr 1
  funext γ
  exact (ENNReal.ofReal_mul hs.le).symm

lemma pantsMinimumLength_gt_iff_prefix_count_zero (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (t : ℝ≥0) :
    (t : ℝ≥0∞)<ENNReal.ofReal s*pantsMinimumLength H X ↔
      (planarLengthPointMeasure H X s hs 2).count ℝ≥0 (nnrealPrefixWindow t)=0 := by
  classical
  let p := fun γ : H.Primitive g n X =>
    ∃S : Finset (Fin n), H.planarSide γ=some S ∧ S.card=2
  letI := curveLengthMeasure_finite_below H X s hs p ((t : ℝ)+1)
  rw [pantsMinimumLength_scaled H X s hs,
    ←ENNReal.ofReal_coe_nnreal]
  change (ENNReal.ofReal (t : ℝ) < ⨅γ : {γ : H.Primitive g n X // p γ},
    ENNReal.ofReal (s*H.length γ.val)) ↔ _
  have hiff := @ofReal_lt_iInf_iff_of_finite_below
    {γ : H.Primitive g n X // p γ}
    (fun γ => s*H.length γ.val) (t : ℝ) t.property
    (curveLengthMeasure_finite_below H X s hs p ((t : ℝ)+1))
  rw [hiff]
  rw [planarLengthPointMeasure_prefix_count H X s hs 2 t]
  have he : H.planarCount X 2 ((t : ℝ)/s)=0 ↔
      ∀γ : {γ : H.Primitive g n X // p γ}, (t : ℝ)<s*H.length γ.val := by
    rw [H.planarCount_eq_card]
    constructor
    · intro hc γ
      by_contra hγ
      have hmem : γ.val ∈ H.shortPlanar X 2 ((t : ℝ)/s) :=
        (H.mem_shortPlanar X 2 _ γ.val).mpr ⟨
          (le_div_iff₀ hs).mpr (by simpa [mul_comm] using le_of_not_gt hγ),γ.property⟩
      have hne := Finset.card_pos.mpr ⟨γ.val,hmem⟩
      omega
    · intro hall
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      have hm := (H.mem_shortPlanar X 2 _ γ).mp hγ
      have hl := (le_div_iff₀ hs).mp hm.1
      exact (not_lt_of_ge (by simpa [mul_comm] using hl)) (hall ⟨γ,hm.2⟩)
  exact he.symm

lemma pantsLengthPointProcess_prefix_count_eq_minimum_void (X : G.Moduli g n (fun _ => 0))
    (t : ℝ≥0) :
    (pantsLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow t)=0 ↔
      (t : ℝ≥0∞)<ENNReal.ofReal (pantsLengthScale g n)*pantsMinimumLength H X :=
  (pantsMinimumLength_gt_iff_prefix_count_zero H X _ (pantsLengthScale_pos g n) t).symm

lemma pantsMinimumLength_measurable :
    Measurable (fun X : G.Moduli g n (fun _ => 0) => pantsMinimumLength H X) := by
  apply measurable_of_Ioi
  intro b
  by_cases hb : b=⊤
  · subst b
    simp
  · have hbt : (b.toNNReal : ℝ≥0∞)=b := ENNReal.coe_toNNReal hb
    have he : {X : G.Moduli g n (fun _ => 0) | b<pantsMinimumLength H X} =
        {X | H.pantsCount X (b.toNNReal : ℝ)=0} := by
      ext X
      rw [←hbt]
      have hiff := pantsMinimumLength_gt_iff_prefix_count_zero H X 1 (by norm_num) b.toNNReal
      simpa only [ENNReal.ofReal_one,one_mul,
        planarLengthPointMeasure_prefix_count,div_one,Set.mem_setOf_eq,
        ENNReal.toNNReal_coe,HyperbolicCurveGeometry.pantsCount] using hiff
    change MeasurableSet {X : G.Moduli g n (fun _ => 0) | b<pantsMinimumLength H X}
    rw [he]
    exact (measurableSet_singleton 0).preimage (H.measurable_pantsCount _)

lemma pantsMinimumLength_eq_top_of_empty (X : G.Moduli g n (fun _ => 0))
    (h : IsEmpty {γ : H.Primitive g n X //
      ∃S : Finset (Fin n), H.planarSide γ=some S ∧ S.card=2}) :
    pantsMinimumLength H X=⊤ := by
  letI := h
  simp [pantsMinimumLength]

end WP.RandomGeometry
