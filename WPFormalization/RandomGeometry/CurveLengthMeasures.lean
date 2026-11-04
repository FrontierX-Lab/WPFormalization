import WPFormalization.RandomGeometry.PantsCounts
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Actual counting measures of scaled primitive geodesic lengths. The complete
geometric length catalog proves local finiteness; no point-process law is assumed. -/
noncomputable section
universe u v w t
namespace WP.RandomGeometry
open WP.External MeasureTheory Filter
open scoped ENNReal Topology

lemma sum_dirac_apply_eq_natCard {α β : Type*} [MeasurableSpace β]
    (f : α → β) (B : Set β) (hB : MeasurableSet B) [Finite {a : α // f a ∈ B}] :
    Measure.sum (fun a => Measure.dirac (f a)) B =
      (Nat.card {a : α // f a ∈ B} : ℝ≥0∞) := by
  classical
  letI : Fintype {a : α // f a ∈ B} := Fintype.ofFinite _
  rw [Measure.sum_apply _ hB]
  calc
    _ = ∑' a : α, ({a : α | f a ∈ B}).indicator (fun _ => (1 : ℝ≥0∞)) a := by
      apply tsum_congr
      intro a
      rw [Measure.dirac_apply' _ hB]
      by_cases ha : f a ∈ B <;> simp [Set.indicator,ha]
    _ = ∑' _ : {a : α | f a ∈ B}, (1 : ℝ≥0∞) :=
      (tsum_subtype {a : α | f a ∈ B} (fun _ => (1 : ℝ≥0∞))).symm
    _ = ∑' _ : {a : α // f a ∈ B}, (1 : ℝ≥0∞) :=
      (show {a : α | f a ∈ B} ≃ {a : α // f a ∈ B} from Equiv.refl _).tsum_eq (fun _ => (1 : ℝ≥0∞))
    _ = _ := by rw [tsum_fintype]; simp [Nat.card_eq_fintype_card]

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

/- The predicate selects actual geometric curves; all multiplicities are one. -/
def curveLengthMeasure (X : G.Moduli g n (fun _ => 0)) (s : ℝ)
    (p : H.Primitive g n X → Prop) : Measure ℝ :=
  Measure.sum (fun γ : {γ : H.Primitive g n X // p γ} => Measure.dirac (s*H.length γ.val))

def primitiveLengthMeasure (X : G.Moduli g n (fun _ => 0)) (s : ℝ) : Measure ℝ :=
  curveLengthMeasure H X s (fun _ => True)

def planarLengthMeasure (X : G.Moduli g n (fun _ => 0)) (s : ℝ) (k : ℕ) : Measure ℝ :=
  curveLengthMeasure H X s (fun γ => ∃S : Finset (Fin n), H.planarSide γ=some S ∧ S.card=k)

lemma curveLengthMeasure_finite_below (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) (B : ℝ) :
    Finite {γ : {γ : H.Primitive g n X // p γ} // s*H.length γ.val ≤ B} := by
  classical
  let f : {γ : {γ : H.Primitive g n X // p γ} // s*H.length γ.val ≤ B} →
      {γ : H.Primitive g n X // γ ∈ H.shortPrimitive X (B/s)} := fun γ =>
    ⟨γ.val.val, (H.mem_shortPrimitive X (B/s) γ.val.val).mpr
      ((le_div_iff₀ hs).mpr (by simpa [mul_comm] using γ.property))⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    change a.val.val=b.val.val at hh
    exact hh)

lemma curveLengthMeasure_Iic (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) (B : ℝ) :
    curveLengthMeasure H X s p (Set.Iic B) =
      (Nat.card {γ : H.Primitive g n X // H.length γ ≤ B/s ∧ p γ} : ℝ≥0∞) := by
  letI : Finite {a : {γ : H.Primitive g n X // p γ} // s*H.length a.val ∈ Set.Iic B} := by
    change Finite {a : {γ : H.Primitive g n X // p γ} // s*H.length a.val ≤ B}
    exact curveLengthMeasure_finite_below H X s hs p B
  rw [curveLengthMeasure,sum_dirac_apply_eq_natCard _ _ measurableSet_Iic]
  congr 1
  apply Nat.card_congr
  exact {
    toFun := fun γ => ⟨γ.val.val,
      (le_div_iff₀ hs).mpr (by simpa [mul_comm] using γ.property),γ.val.property⟩
    invFun := fun γ => ⟨⟨γ.val,γ.property.2⟩,
      by simpa [mul_comm] using (le_div_iff₀ hs).mp γ.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma primitiveLengthMeasure_Iic (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (B : ℝ) :
    primitiveLengthMeasure H X s (Set.Iic B) = (H.primitiveCount X (B/s) : ℝ≥0∞) := by
  rw [primitiveLengthMeasure,curveLengthMeasure_Iic H X s hs]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ => by simp))

lemma planarLengthMeasure_Iic (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (k : ℕ) (B : ℝ) :
    planarLengthMeasure H X s k (Set.Iic B) = (H.planarCount X k (B/s) : ℝ≥0∞) :=
  curveLengthMeasure_Iic H X s hs _ B

lemma curveLengthMeasure_isLocallyFinite (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) :
    IsLocallyFiniteMeasure (curveLengthMeasure H X s p) := by
  constructor
  intro x
  refine ⟨Set.Iic (x+1),Iic_mem_nhds (by linarith),?_⟩
  rw [curveLengthMeasure_Iic H X s hs p]
  exact ENNReal.natCast_lt_top _

lemma curveLengthMeasure_Iic_zero (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) :
    curveLengthMeasure H X s p (Set.Iic 0)=0 := by
  classical
  unfold curveLengthMeasure
  rw [Measure.sum_apply _ measurableSet_Iic]
  apply ENNReal.tsum_eq_zero.mpr
  intro γ
  rw [Measure.dirac_apply' _ measurableSet_Iic]
  apply Set.indicator_of_notMem
  simpa only [Set.mem_Iic,not_le] using mul_pos hs (H.length_pos γ.val)

lemma primitiveLengthMeasure_prefix_measurable (s : ℝ) (hs : 0<s) (B : ℝ) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      primitiveLengthMeasure H X s (Set.Iic B)) := by
  simp_rw [primitiveLengthMeasure_Iic H _ s hs B]
  exact (measurable_of_countable (fun N : ℕ => (N : ℝ≥0∞))).comp
    (H.measurable_primitiveCount g n (B/s))

lemma planarLengthMeasure_prefix_measurable (s : ℝ) (hs : 0<s) (k : ℕ) (B : ℝ) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      planarLengthMeasure H X s k (Set.Iic B)) := by
  simp_rw [planarLengthMeasure_Iic H _ s hs k B]
  exact (measurable_of_countable (fun N : ℕ => (N : ℝ≥0∞))).comp
    (H.measurable_planarCount g n k (B/s))

end WP.RandomGeometry
