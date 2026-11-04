import WPFormalization.External.TightGeodesicBorelModel
import WPFormalization.Tight.SpectrumTupleExtensions
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/- Appendix F.4 measurability deductions from the approved countable marked
homotopy-class Borel model. Unique tightness is still the actual Q.IsTight
definition. The full primitive count uses exactly H.Primitive, including
nonsimple curves. Countability, measurable comparisons, Mathlib.measurable_ncard
and quotient descent prove all conclusions locally; none is an interface field. -/
noncomputable section
universe u v w z

namespace WP.Tight
open External Set MeasureTheory
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Q : TightGeodesicGeometry G T H} {g n : ℕ} {hg : 2 ≤ g}
  (B : TightGeodesicBorelModel G T H Q g n hg)
include B

lemma label_tight_iff (Y : B.Marked) (a : B.Label) :
    Q.IsTight (B.labelEquiv Y a) ↔ B.nonnullLabel a ∧
      ∀ b : B.Label, B.sameCapLabel b a →
        Q.length (B.labelEquiv Y b) ≤ Q.length (B.labelEquiv Y a) → b = a := by
  constructor
  · intro ht
    refine ⟨(B.nonnull_iff Y a).mp ht.1, ?_⟩
    intro b hcap hlen
    exact (B.labelEquiv Y).injective (ht.2 _ ((B.sameCap_iff Y b a).mpr hcap) hlen)
  · rintro ⟨hnonnull, hmin⟩
    refine ⟨(B.nonnull_iff Y a).mpr hnonnull, ?_⟩
    intro δ hcap hlen
    obtain ⟨b, rfl⟩ := (B.labelEquiv Y).surjective δ
    exact congrArg (B.labelEquiv Y) (hmin b ((B.sameCap_iff Y b a).mp hcap) hlen)

lemma measurableSet_label_tight (a : B.Label) :
    MeasurableSet {Y : B.Marked | Q.IsTight (B.labelEquiv Y a)} := by
  simp_rw [label_tight_iff B]
  by_cases hn : B.nonnullLabel a
  · simp only [hn, true_and]
    have hset : ∀ b : B.Label, MeasurableSet {Y : B.Marked |
        B.sameCapLabel b a →
          Q.length (B.labelEquiv Y b) ≤ Q.length (B.labelEquiv Y a) → b = a} := by
      intro b
      by_cases hcap : B.sameCapLabel b a
      · by_cases hba : b = a
        · simp only [hba, implies_true, setOf_true]
          exact MeasurableSet.univ
        · have hc := (measurableSet_le (B.length_measurable b) (B.length_measurable a)).compl
          change MeasurableSet {Y : B.Marked |
            ¬ Q.length (B.labelEquiv Y b) ≤ Q.length (B.labelEquiv Y a)} at hc
          simpa only [hcap, true_implies, hba, imp_false] using hc
      · simp only [hcap, false_implies, setOf_true]
        exact MeasurableSet.univ
    simpa only [setOf_forall] using MeasurableSet.iInter hset
  · simp only [hn, false_and, setOf_false]
    exact MeasurableSet.empty

lemma measurable_marked_tight_ncard (I : Set ℝ) (hI : MeasurableSet I) :
    Measurable (fun Y : B.Marked =>
      ({a : B.Label | B.primitiveLabel a ∧ Q.IsTight (B.labelEquiv Y a) ∧
        Q.length (B.labelEquiv Y a) ∈ I}).ncard) := by
  apply measurable_ncard.comp
  apply measurable_pi_lambda
  intro a
  apply measurable_to_prop
  have hset : MeasurableSet {Y : B.Marked | B.primitiveLabel a ∧
      Q.IsTight (B.labelEquiv Y a) ∧ Q.length (B.labelEquiv Y a) ∈ I} := by
    by_cases hp : B.primitiveLabel a
    · have hc := (measurableSet_label_tight B a).inter ((B.length_measurable a) hI)
      change MeasurableSet {Y : B.Marked | Q.IsTight (B.labelEquiv Y a) ∧
        Q.length (B.labelEquiv Y a) ∈ I} at hc
      simpa only [hp, true_and] using hc
    · simp only [hp, false_and, setOf_false]
      exact MeasurableSet.empty
  change MeasurableSet {Y : B.Marked | (B.primitiveLabel a ∧
    Q.IsTight (B.labelEquiv Y a) ∧ Q.length (B.labelEquiv Y a) ∈ I) = True}
  simpa only [eq_iff_iff, iff_true] using hset



def tightLabelEquivActual (Y : B.Marked) (I : Set ℝ) :
    {a : B.Label // B.primitiveLabel a ∧ Q.IsTight (B.labelEquiv Y a) ∧
      Q.length (B.labelEquiv Y a) ∈ I} ≃
    {γ : H.Primitive g n (tightCuspSurface G (B.forget Y)) //
      Q.cuspTight (B.forget Y) γ ∧ H.length γ ∈ I} where
  toFun a := by
    let γ : {γ : Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) (B.forget Y) //
      Q.primitive γ} := ⟨B.labelEquiv Y a.val, (B.primitive_iff Y a.val).mpr a.property.1⟩
    refine ⟨Q.cuspPrimitiveEquiv g n (B.forget Y) γ, ?_, ?_⟩
    · simpa only [TightGeodesicGeometry.cuspTight, Equiv.symm_apply_apply]
        using a.property.2.1
    · rw [Q.cuspPrimitive_length]
      exact a.property.2.2
  invFun γ := by
    let γ' := (Q.cuspPrimitiveEquiv g n (B.forget Y)).symm γ.val
    let a := (B.labelEquiv Y).symm γ'.val
    have ha : B.labelEquiv Y a = γ'.val := (B.labelEquiv Y).apply_symm_apply _
    refine ⟨a, ?_, ?_, ?_⟩
    · apply (B.primitive_iff Y a).mp
      rw [ha]
      exact γ'.property
    · rw [ha]
      exact γ.property.1
    · rw [ha]
      have hl := Q.cuspPrimitive_length g n (B.forget Y) γ'
      rw [Equiv.apply_symm_apply] at hl
      rw [←hl]
      exact γ.property.2
  left_inv a := by
    apply Subtype.ext
    dsimp
    simp only [Equiv.symm_apply_apply]
  right_inv γ := by
    apply Subtype.ext
    dsimp
    simp only [Equiv.apply_symm_apply]
    change (Q.cuspPrimitiveEquiv g n (B.forget Y))
      ((Q.cuspPrimitiveEquiv g n (B.forget Y)).symm γ.val) = γ.val
    exact (Q.cuspPrimitiveEquiv g n (B.forget Y)).apply_symm_apply γ.val

lemma actual_tight_count_eq_marked_ncard (Y : B.Marked) (I : Set ℝ) :
    Q.cuspTightCount (B.forget Y) I =
      ({a : B.Label | B.primitiveLabel a ∧ Q.IsTight (B.labelEquiv Y a) ∧
        Q.length (B.labelEquiv Y a) ∈ I}).ncard := by
  rw [←Nat.card_coe_set_eq]
  exact (Nat.card_congr (tightLabelEquivActual B Y I)).symm

/- Full primitive tight count measurability follows from countable marked
classes and the unchanged unique-minimum predicate, then quotient descent. -/
theorem measurable_actual_tight_count (I : Set ℝ) (hI : MeasurableSet I) :
    Measurable (fun X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) =>
      Q.cuspTightCount X I) := by
  have hf : Measurable (fun Y : B.Marked => Q.cuspTightCount (B.forget Y) I) := by
    convert measurable_marked_tight_ncard B I hI using 1
    funext Y
    exact actual_tight_count_eq_marked_ncard B Y I
  intro S hS
  apply B.measurableSet_descend
  exact hf hS



lemma bad_configuration_iff_marked (Y : B.Marked) (b : ℝ) :
    SpectrumTupleExtensions.BadConfiguration Q (B.forget Y) b ↔
      (∃ a : B.Label, B.primitiveLabel a ∧ Q.IsTight (B.labelEquiv Y a) ∧
        Q.length (B.labelEquiv Y a) ≤ b ∧ ¬B.simpleLabel a) ∨
      ∃ a c : B.Label, a ≠ c ∧ B.primitiveLabel a ∧ B.primitiveLabel c ∧
        Q.IsTight (B.labelEquiv Y a) ∧ Q.IsTight (B.labelEquiv Y c) ∧
        Q.length (B.labelEquiv Y a) ≤ b ∧ Q.length (B.labelEquiv Y c) ≤ b ∧
        ¬B.disjointLabel a c := by
  simp only [SpectrumTupleExtensions.BadConfiguration,
    (B.labelEquiv Y).symm.exists_congr_left, Equiv.symm_symm, B.primitive_iff,
    B.simple_iff, B.disjoint_iff, ne_eq, Equiv.apply_eq_iff_eq]

theorem measurableSet_actual_bad_configuration (b : ℝ) :
    MeasurableSet {X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) |
      SpectrumTupleExtensions.BadConfiguration Q X b} := by
  apply B.measurableSet_descend
  change MeasurableSet {Y : B.Marked |
    SpectrumTupleExtensions.BadConfiguration Q (B.forget Y) b}
  simp_rw [bad_configuration_iff_marked B]
  apply MeasurableSet.union
  · apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro a
    apply measurableSet_setOfPred.mp
    have hm : MeasurableSet {Y : B.Marked | Q.IsTight (B.labelEquiv Y a) ∧
        Q.length (B.labelEquiv Y a) ≤ b} :=
      (measurableSet_label_tight B a).inter (measurableSet_le (B.length_measurable a) (measurable_const (a:=b)))
    by_cases hp : B.primitiveLabel a ∧ ¬B.simpleLabel a
    · rcases hp with ⟨hp, hs⟩
      simpa only [hp, hs, not_false_eq_true, true_and, and_true] using hm
    · have hempty : {Y : B.Marked | B.primitiveLabel a ∧
          Q.IsTight (B.labelEquiv Y a) ∧ Q.length (B.labelEquiv Y a) ≤ b ∧
          ¬B.simpleLabel a} = ∅ := by
        ext Y
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        tauto
      rw [hempty]
      exact MeasurableSet.empty
  · apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro a
    apply Measurable.exists
    intro c
    apply measurableSet_setOfPred.mp
    have hm : MeasurableSet {Y : B.Marked | Q.IsTight (B.labelEquiv Y a) ∧
        Q.IsTight (B.labelEquiv Y c) ∧ Q.length (B.labelEquiv Y a) ≤ b ∧
        Q.length (B.labelEquiv Y c) ≤ b} :=
      (measurableSet_label_tight B a).inter ((measurableSet_label_tight B c).inter
        ((measurableSet_le (B.length_measurable a) (measurable_const (a:=b))).inter
          (measurableSet_le (B.length_measurable c) (measurable_const (a:=b)))))
    by_cases hp : a ≠ c ∧ B.primitiveLabel a ∧ B.primitiveLabel c ∧ ¬B.disjointLabel a c
    · rcases hp with ⟨hne, hpa, hpc, hdisj⟩
      simpa only [ne_eq, hne, hpa, hpc, hdisj, not_false_eq_true, true_and, and_true] using hm
    · have hempty : {Y : B.Marked | a ≠ c ∧ B.primitiveLabel a ∧ B.primitiveLabel c ∧
          Q.IsTight (B.labelEquiv Y a) ∧ Q.IsTight (B.labelEquiv Y c) ∧
          Q.length (B.labelEquiv Y a) ≤ b ∧ Q.length (B.labelEquiv Y c) ≤ b ∧
          ¬B.disjointLabel a c} = ∅ := by
        ext Y
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        tauto
      rw [hempty]
      exact MeasurableSet.empty



theorem measurableSet_actual_hasShortTight (b : ℝ) :
    MeasurableSet {X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) |
      SpectrumTupleExtensions.HasShortTight Q X b} := by
  have hset := (measurable_actual_tight_count B (Iic b) measurableSet_Iic)
    (measurableSet_Ioi (a:=(0:ℕ)))
  change MeasurableSet {X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) |
    0 < Q.cuspTightCount X (Iic b)} at hset
  simpa only [SpectrumTupleExtensions.hasShortTight_iff_actual_count_pos] using hset

lemma measurableSet_marked_exists_filtered_tight (R : B.Label → Prop) (b : ℝ) :
    MeasurableSet {Y : B.Marked | ∃ a : B.Label, R a ∧
      Q.IsTight (B.labelEquiv Y a) ∧ Q.length (B.labelEquiv Y a) ≤ b} := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.exists
  intro a
  apply measurableSet_setOfPred.mp
  by_cases hR : R a
  · have hc := (measurableSet_label_tight B a).inter
      (measurableSet_le (B.length_measurable a) (measurable_const (a:=b)))
    change MeasurableSet {Y : B.Marked | Q.IsTight (B.labelEquiv Y a) ∧
      Q.length (B.labelEquiv Y a) ≤ b} at hc
    simpa only [hR, true_and] using hc
  · simp only [hR, false_and, setOf_false]
    exact MeasurableSet.empty

theorem measurableSet_actual_hasShortSimple (b : ℝ) :
    MeasurableSet {X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) |
      SpectrumTupleExtensions.HasShortSimple Q X b} := by
  apply B.measurableSet_descend
  have heq : (B.forget ⁻¹' {X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) |
        SpectrumTupleExtensions.HasShortSimple Q X b}) =
      {Y : B.Marked | ∃ a : B.Label, (B.primitiveLabel a ∧ B.simpleLabel a) ∧
        Q.IsTight (B.labelEquiv Y a) ∧ Q.length (B.labelEquiv Y a) ≤ b} := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, SpectrumTupleExtensions.HasShortSimple,
      (B.labelEquiv Y).symm.exists_congr_left, Equiv.symm_symm, B.primitive_iff, B.simple_iff,
      and_assoc, and_left_comm, and_comm]
  rw [heq]
  exact measurableSet_marked_exists_filtered_tight B _ b

end WP.Tight
