import WPFormalization.Analysis.ComplexGermGluing
/-! Common-radius local holomorphic coefficient families with Gevrey bounds glue to ONE complex neighborhood. Actual overlap agreement is proved before choosing the family; a finite subcover supplies constants uniform in every coefficient order. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma exists_common_bounded_complex_family_extension (a b : ℝ) (v : ℕ → ℝ → ℂ)
    (hlocal : ∀ x ∈ Icc a b, ∃ r C B : ℝ, 0 < r ∧ 0 < C ∧ 0 < B ∧
      ∃ f : ℕ → ℂ → ℂ,
        (∀ j, AnalyticOnNhd ℂ (f j) (Metric.ball (x : ℂ) r)) ∧
        (∀ j t, t ∈ Icc a b → (t : ℂ) ∈ Metric.ball (x : ℂ) r → f j (t : ℂ) = v j t) ∧
        ∀ j z, z ∈ Metric.ball (x : ℂ) r → ‖f j z‖ ≤ C * B^j * (j.factorial : ℝ)^2) :
    ∃ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (C B : ℝ), IsOpen Ω ∧
      (∀ x ∈ Icc a b, (x : ℂ) ∈ Ω) ∧ 0 < C ∧ 0 < B ∧
      (∀ j, AnalyticOnNhd ℂ (F j) Ω) ∧
      (∀ j x, x ∈ Icc a b → F j (x : ℂ) = v j x) ∧
      ∀ j z, z ∈ Ω → ‖F j z‖ ≤ C * B^j * (j.factorial : ℝ)^2 := by
  classical
  choose r C B hr hC hB f hfa hfr hfb using fun x : Icc a b => hlocal x x.property
  have hcompat (i k : Icc a b) (j : ℕ) : EqOn (f i j) (f k j)
      (Metric.ball ((i : ℝ) : ℂ) (r i) ∩ Metric.ball ((k : ℝ) : ℂ) (r k)) := by
    rcases lt_trichotomy (i : ℝ) (k : ℝ) with hik | hik | hki
    · exact complex_ball_overlap_identity_ordered a b i k (r i) (r k) i.property k.property hik
        (hr i) (hr k) (f i j) (f k j) (v j) (hfa i j) (hfa k j) (hfr i j) (hfr k j)
    · have he : i = k := Subtype.ext hik
      subst k
      exact fun z hz => rfl
    · have he := complex_ball_overlap_identity_ordered a b k i (r k) (r i) k.property i.property hki
        (hr k) (hr i) (f k j) (f i j) (v j) (hfa k j) (hfa i j) (hfr k j) (hfr i j)
      exact fun z hz => (he ⟨hz.2,hz.1⟩).symm
  let K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun i : Icc a b => Metric.ball ((i : ℝ) : ℂ) (r i))
    (fun i => Metric.isOpen_ball) (by
      rintro z ⟨x,hx,rfl⟩
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (hr ⟨x,hx⟩)⟩)
  let Ω : Set ℂ := ⋃ i ∈ t, Metric.ball ((i : ℝ) : ℂ) (r i)
  let F : ℕ → ℂ → ℂ := fun j z => if hz : z ∈ Ω then f (Classical.choose (mem_iUnion₂.mp hz)) j z else 0
  let C0 : ℝ := 1 + ∑ i ∈ t, C i
  let B0 : ℝ := 1 + ∑ i ∈ t, B i
  have hC0 : 0 < C0 := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i hi => (hC i).le))
  have hB0 : 0 < B0 := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i hi => (hB i).le))
  have hCle (i : Icc a b) (hi : i ∈ t) : C i ≤ C0 := by
    have he := Finset.single_le_sum (f := C) (fun k hk => (hC k).le) hi
    change C i ≤ 1 + ∑ k ∈ t, C k
    linarith only [he]
  have hBle (i : Icc a b) (hi : i ∈ t) : B i ≤ B0 := by
    have he := Finset.single_le_sum (f := B) (fun k hk => (hB k).le) hi
    change B i ≤ 1 + ∑ k ∈ t, B k
    linarith only [he]
  have hEq (i : Icc a b) (hi : i ∈ t) (j : ℕ) : EqOn (F j) (f i j) (Metric.ball ((i : ℝ) : ℂ) (r i)) := by
    intro z hz
    have hzΩ : z ∈ Ω := mem_iUnion₂.mpr ⟨i,hi,hz⟩
    dsimp only [F]
    rw [dite_eq_left hzΩ]
    exact hcompat _ i j ⟨(Classical.choose_spec (mem_iUnion₂.mp hzΩ)).2,hz⟩
  refine ⟨Ω,F,C0,B0,isOpen_iUnion (fun i => isOpen_iUnion (fun hi => Metric.isOpen_ball)),
    (fun x hx => ht ⟨x,hx,rfl⟩),hC0,hB0,?_,?_,?_⟩
  · intro j z hz
    obtain ⟨i,hi,hz⟩ := mem_iUnion₂.mp hz
    apply (hfa i j z hz).congr
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact (hEq i hi j hw).symm
  · intro j x hx
    obtain ⟨i,hi,hz⟩ := mem_iUnion₂.mp (ht ⟨x,hx,rfl⟩)
    exact (hEq i hi j hz).trans (hfr i j x hx hz)
  · intro j z hz
    obtain ⟨i,hi,hz⟩ := mem_iUnion₂.mp hz
    rw [hEq i hi j hz]
    exact (hfb i j z hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (hCle i hi) (pow_le_pow_left₀ (hB i).le (hBle i hi) _) (pow_nonneg (hB i).le _) hC0.le) (sq_nonneg _))
end WP.Analysis
