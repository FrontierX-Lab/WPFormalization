import WPFormalization.Probability.PointMeasureDefinitions
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

noncomputable section
namespace WP.Probability
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

/-- Half-open rational intervals in the nonnegative line. Negative lower
endpoints give the prefix windows that contain the origin. -/
def nnrealRationalWindow (a b : ℚ) : RelCompactBorelWindow ℝ≥0 where
  carrier := (fun x : ℝ≥0 => (x : ℝ)) ⁻¹' Ioc (a : ℝ) (b : ℝ)
  measurableSet := (measurableSet_Ioc).preimage NNReal.continuous_coe.measurable
  compactClosure := by
    apply (isCompact_Icc (a := (0 : ℝ≥0)) (b := Real.toNNReal b)).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_Icc
    intro x hx
    refine ⟨bot_le, ?_⟩
    change (x : ℝ) ≤ (Real.toNNReal (b : ℝ) : ℝ)
    exact hx.2.trans (Real.le_coe_toNNReal _)

@[simp] theorem mem_nnrealRationalWindow {a b : ℚ} {x : ℝ≥0} :
    x ∈ (nnrealRationalWindow a b).carrier ↔ (a : ℝ) < x ∧ (x : ℝ) ≤ b := Iff.rfl

def nnrealRationalWindows : Set (RelCompactBorelWindow ℝ≥0) :=
  Set.range (fun ab : ℚ × ℚ => nnrealRationalWindow ab.1 ab.2)

theorem nnrealRationalWindows_countable : nnrealRationalWindows.Countable :=
  Set.countable_range _

@[simp] theorem nnrealRationalWindow_empty (a : ℚ) :
    (nnrealRationalWindow a a).carrier = ∅ := by
  ext x
  simp

theorem nnrealRationalWindow_inter (a b c d : ℚ) :
    (nnrealRationalWindow (max a c) (min b d)).carrier =
      (nnrealRationalWindow a b).carrier ∩ (nnrealRationalWindow c d).carrier := by
  ext x
  simp only [mem_inter_iff, mem_nnrealRationalWindow, Rat.cast_max, Rat.cast_min,
    max_lt_iff, le_min_iff]
  tauto

theorem nnrealRationalWindow_diff (a b c d : ℚ) (hcd : c ≤ d) :
    (nnrealRationalWindow a b).carrier \ (nnrealRationalWindow c d).carrier =
      (nnrealRationalWindow a (min b c)).carrier ∪
      (nnrealRationalWindow (max a d) b).carrier := by
  ext x
  have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd
  simp only [Set.mem_sdiff, mem_union, mem_nnrealRationalWindow, Rat.cast_max,
    Rat.cast_min, max_lt_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hax, hxb⟩, hnot⟩
    by_cases hxc : (x : ℝ) ≤ c
    · exact Or.inl ⟨hax, hxb, hxc⟩
    · exact Or.inr ⟨⟨hax, lt_of_not_ge (fun hxd => hnot ⟨lt_of_not_ge hxc, hxd⟩)⟩, hxb⟩
  · rintro (⟨hax, hxb, hxc⟩ | ⟨⟨hax, hdx⟩, hxb⟩)
    · exact ⟨⟨hax, hxb⟩, fun hx => (not_lt_of_ge hxc) hx.1⟩
    · exact ⟨⟨hax, hxb⟩, fun hx => (not_lt_of_ge hx.2) hdx⟩

theorem nnrealRationalWindow_diff_disjoint (a b c d : ℚ) (hcd : c ≤ d) :
    Disjoint (nnrealRationalWindow a (min b c)).carrier
      (nnrealRationalWindow (max a d) b).carrier := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd
  simp only [mem_nnrealRationalWindow, Rat.cast_max, Rat.cast_min, max_lt_iff,
    le_min_iff] at hx hy
  exact (not_lt_of_ge (hx.2.2.trans hcd')) hy.1.2

theorem nnrealRationalWindow_continuity (ν : Measure ℝ≥0) [NullSingletonClass ν]
    (a b : ℚ) : ν (frontier (nnrealRationalWindow a b).carrier) = 0 := by
  by_cases hab : a < b
  · have hab' : (a : ℝ) < b := by exact_mod_cast hab
    apply measure_mono_null (NNReal.continuous_coe.frontier_preimage_subset _)
    rw [frontier_Ioc hab']
    have hnull (c : ℝ) : ν ((fun x : ℝ≥0 => (x : ℝ)) ⁻¹' {c}) = 0 := by
      by_cases hc : 0 ≤ c
      · have he : (fun x : ℝ≥0 => (x : ℝ)) ⁻¹' {c} = {⟨c, hc⟩} := by
          ext x
          change ((x : ℝ) = c) ↔ x = (⟨c, hc⟩ : ℝ≥0)
          constructor
          · intro hx
            exact Subtype.ext hx
          · intro hx
            exact congrArg Subtype.val hx
        rw [he]
        exact measure_singleton _
      · have he : (fun x : ℝ≥0 => (x : ℝ)) ⁻¹' {c} = ∅ := by
          ext x
          simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
          intro h
          exact hc (h ▸ x.2)
        rw [he, measure_empty]
    change ν ((fun x : ℝ≥0 => (x : ℝ)) ⁻¹' ({(a : ℝ)} ∪ {(b : ℝ)})) = 0
    rw [preimage_union]
    exact measure_union_null (hnull a) (hnull b)
  · have he : (nnrealRationalWindow a b).carrier = ∅ := by
      ext x
      simp only [mem_nnrealRationalWindow, mem_empty_iff_false, iff_false, not_and]
      intro hax hxb
      apply hab
      exact_mod_cast hax.trans_le hxb
    rw [he, frontier_empty, measure_empty]

/-- Rational half-open windows form neighborhoods even at the origin. -/
theorem exists_nnrealRationalWindow (U : Set ℝ≥0) (hU : IsOpen U)
    (x : ℝ≥0) (hx : x ∈ U) :
    ∃ a b : ℚ, x ∈ interior (nnrealRationalWindow a b).carrier ∧
      (nnrealRationalWindow a b).carrier ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨a, haxε, hax⟩ := exists_rat_btwn (show (x : ℝ) - ε < x by linarith)
  obtain ⟨b, hxb, hbxε⟩ := exists_rat_btwn (show (x : ℝ) < x + ε by linarith)
  refine ⟨a, b, ?_, ?_⟩
  · apply (isOpen_Ioo.preimage NNReal.continuous_coe).subset_interior_iff.mpr ?_ ⟨hax, hxb⟩
    intro y hy
    exact ⟨hy.1, hy.2.le⟩
  · intro y hy
    apply hball
    rw [Metric.mem_ball, NNReal.dist_eq, abs_lt]
    have hy' : (a : ℝ) < y ∧ (y : ℝ) ≤ b := hy
    exact ⟨by linarith [hy'.1], by linarith [hy'.2]⟩

theorem nnrealRationalWindow_empty_of_ge (a b : ℚ) (hab : b ≤ a) :
    (nnrealRationalWindow a b).carrier = ∅ := by
  ext x
  simp only [mem_nnrealRationalWindow, mem_empty_iff_false, iff_false, not_and]
  intro hax hxb
  have hab' : (b : ℝ) ≤ a := by exact_mod_cast hab
  exact (not_lt_of_ge (hxb.trans hab')) hax

/-- The rational half-open windows, including prefixes through zero, are a
countable continuity semiring for any diffuse measure on the half-line. -/
theorem nnrealRationalWindows_basis (ν : Measure ℝ≥0) [NullSingletonClass ν] :
    ContinuityWindowBasis ℝ≥0 ν nnrealRationalWindows := by
  classical
  refine ⟨nnrealRationalWindows_countable, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨nnrealRationalWindow 0 0, ⟨(0, 0), rfl⟩,
      nnrealRationalWindow_empty 0⟩
  · rintro A ⟨⟨a, b⟩, rfl⟩ B ⟨⟨c, d⟩, rfl⟩
    exact ⟨nnrealRationalWindow (max a c) (min b d),
      ⟨(max a c, min b d), rfl⟩, nnrealRationalWindow_inter a b c d⟩
  · rintro A ⟨⟨a, b⟩, rfl⟩ B ⟨⟨c, d⟩, rfl⟩
    by_cases hcd : c ≤ d
    · let L := nnrealRationalWindow a (min b c)
      let R := nnrealRationalWindow (max a d) b
      refine ⟨{L, R}, ?_, ?_, ?_⟩
      · intro C hC
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC
        rcases hC with rfl | rfl
        · exact ⟨(a, min b c), rfl⟩
        · exact ⟨(max a d, b), rfl⟩
      · intro C hC D hD hne
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC hD
        rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
        · exact False.elim (hne rfl)
        · exact nnrealRationalWindow_diff_disjoint a b c d hcd
        · exact (nnrealRationalWindow_diff_disjoint a b c d hcd).symm
        · exact False.elim (hne rfl)
      · rw [nnrealRationalWindow_diff a b c d hcd]
        ext x
        simp [L, R]
    · refine ⟨{nnrealRationalWindow a b}, ?_, ?_, ?_⟩
      · intro C hC
        simp only [Finset.mem_singleton] at hC
        subst C
        exact ⟨(a, b), rfl⟩
      · intro C hC D hD hne
        simp only [Finset.mem_singleton] at hC hD
        exact False.elim (hne (hC.trans hD.symm))
      · rw [nnrealRationalWindow_empty_of_ge c d (le_of_not_ge hcd), sdiff_empty]
        simp
  · rintro B ⟨⟨a, b⟩, rfl⟩
    exact nnrealRationalWindow_continuity ν a b
  · intro K U hK hU hKU
    let I := {ab : ℚ × ℚ // (nnrealRationalWindow ab.1 ab.2).carrier ⊆ U}
    let W : I → RelCompactBorelWindow ℝ≥0 :=
      fun i => nnrealRationalWindow i.val.1 i.val.2
    have hcover : K ⊆ ⋃ i : I, interior (W i).carrier := by
      intro x hx
      obtain ⟨a, b, hxi, hsub⟩ := exists_nnrealRationalWindow U hU x (hKU hx)
      exact mem_iUnion.mpr ⟨⟨(a, b), hsub⟩, hxi⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover
      (fun i : I => interior (W i).carrier) (fun _ => isOpen_interior) hcover
    refine ⟨t.image W, ?_, ?_, ?_⟩
    · intro B hB
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      exact ⟨i.val, rfl⟩
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
      exact interior_mono (subset_biUnion_of_mem
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩)) hxi
    · intro x hx
      obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
      exact i.property hxB

/-- A canonical bounded half-open window on the half-line. -/
def nnrealIocWindow (a b : ℝ≥0) : RelCompactBorelWindow ℝ≥0 where
  carrier := Ioc a b
  measurableSet := measurableSet_Ioc
  compactClosure := (isCompact_Icc (a := a) (b := b)).of_isClosed_subset
    isClosed_closure (closure_minimal Ioc_subset_Icc_self isClosed_Icc)

theorem PointMeasure.count_mono {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (ξ : PointMeasure E) (A B : RelCompactBorelWindow E) (hAB : A.carrier ⊆ B.carrier) :
    ξ.count E A ≤ ξ.count E B := by
  have h := measure_mono (μ := ξ.toMeasure) hAB
  rw [ξ.count_spec E A, ξ.count_spec E B] at h
  exact_mod_cast h

theorem PointMeasure.count_empty {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (ξ : PointMeasure E) (A : RelCompactBorelWindow E) (hA : A.carrier = ∅) :
    ξ.count E A = 0 := by
  have h := ξ.count_spec E A
  rw [hA, measure_empty] at h
  exact_mod_cast h.symm

/-- Genuine counts in `(a,b]` are differences of genuine compact prefix counts.
No atomlessness assumption is needed. The formula also covers empty windows. -/
theorem PointMeasure.count_nnrealIoc (ξ : PointMeasure ℝ≥0) (a b : ℝ≥0) :
    ξ.count ℝ≥0 (nnrealIocWindow a b) =
      ξ.count ℝ≥0 (nnrealPrefixWindow b) - ξ.count ℝ≥0 (nnrealPrefixWindow a) := by
  by_cases hab : a ≤ b
  · have hdis : Disjoint (Iic a) (Ioc a b) :=
      Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx) hy.1)
    have hsum : ξ.toMeasure (Iic b) = ξ.toMeasure (Iic a) + ξ.toMeasure (Ioc a b) := by
      rw [← Iic_union_Ioc_eq_Iic hab]
      exact measure_union hdis measurableSet_Ioc
    change ξ.toMeasure (nnrealPrefixWindow b).carrier =
      ξ.toMeasure (nnrealPrefixWindow a).carrier +
      ξ.toMeasure (nnrealIocWindow a b).carrier at hsum
    rw [ξ.count_spec ℝ≥0 _, ξ.count_spec ℝ≥0 _, ξ.count_spec ℝ≥0 _] at hsum
    have hn : ξ.count ℝ≥0 (nnrealPrefixWindow b) =
        ξ.count ℝ≥0 (nnrealPrefixWindow a) + ξ.count ℝ≥0 (nnrealIocWindow a b) := by
      exact_mod_cast hsum
    omega
  · have hba : b ≤ a := le_of_not_ge hab
    have hm := ξ.count_mono (nnrealPrefixWindow b) (nnrealPrefixWindow a)
      (Iic_subset_Iic.mpr hba)
    rw [Nat.sub_eq_zero_of_le hm]
    exact ξ.count_empty _ (Ioc_eq_empty_of_le hba)

theorem aemeasurable_nnrealIoc_counts_of_prefix {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Ξ : Ω → PointMeasure ℝ≥0)
    (hcounts : ∀ b : ℝ≥0,
      AEMeasurable (fun ω => (Ξ ω).count ℝ≥0 (nnrealPrefixWindow b)) μ)
    (a b : ℝ≥0) :
    AEMeasurable (fun ω => (Ξ ω).count ℝ≥0 (nnrealIocWindow a b)) μ := by
  simp_rw [PointMeasure.count_nnrealIoc]
  exact (hcounts b).sub (hcounts a)

end WP.Probability
