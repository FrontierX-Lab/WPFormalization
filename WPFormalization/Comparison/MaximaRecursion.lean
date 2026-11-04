import WPFormalization.Comparison.WeightedUpperRecursion
import WPFormalization.Comparison.ClippedMaxima
import WPFormalization.Comparison.RecordGrowth
import WPFormalization.Comparison.MaximaRates
/-! Actual clipped maxima in the positive recursion and at record points.
The signed valid-model support gives genuine lower child complexities and exact
separating rank sums. The maximizing state is attained and is permuted to an
actual PivotChoice. Terminal, linear-row, and separating-row bounds are explicit
inputs supplied by the already proved original theorems; no scalar surrogate
or additional hypothesis is imposed on the original comparison theorem.
The square-root record statement keeps the exact exponential step, and its
separating constant is independent of the barrier parameter A. -/
noncomputable section
namespace WP.Comparison
lemma clippedRatio_le_maximum (P : PsiTheory) (c Y : ℝ) (g : ℕ) (ds : List ℤ)
    (hY : Y ∈ Set.Icc 0 y₀) (hn : 1 ≤ ds.length) (hv : validModel g ds Y ≠ 0) :
    ratio P g (ds.map Int.toNat) Y/signedWeight c ds ≤
      clippedComplexityMaximum P c (complexity g ds.length) := by
  have hs := validModel_ne_zero_support g ds Y hv
  have he := clippedComplexityMaximum_quotient_bound P c g (ds.map Int.toNat)
    (by simpa only [List.length_map] using hn) (by simpa only [List.length_map] using hs.2.1)
    (by simpa only [List.length_map] using hs.2.2) Y hY
  simpa only [List.length_map,signedWeight] using he
lemma merger_child_rank (g pivot : ℕ) (d : List ℕ) (j l : ℕ) (hg : 2 ≤ g) (hj : j < d.length) :
    complexity g (((pivot : ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat).length =
      complexity g (d.length+1)-1 := by
  simp only [List.length_cons,List.length_map,List.length_eraseIdx_of_lt hj]
  unfold complexity
  omega
lemma contraction_child_rank (g pivot : ℕ) (d : List ℕ) (l u : ℕ) (hg : 2 ≤ g) :
    complexity (g-1) ((u : ℤ)::((pivot : ℤ)+l-2-u)::d.map Int.ofNat).length =
      complexity g (d.length+1)-1 := by
  simp only [List.length_cons,List.length_map]
  unfold complexity
  omega
lemma separating_child_ranks (g pivot : ℕ) (d : List ℕ) (l u i : ℕ) (I : Finset ℕ) (hi : i ≤ g)
    (Y : ℝ)
    (hv₁ : validModel i ((u : ℤ)::selected (d.map Int.ofNat) I) Y ≠ 0)
    (hv₂ : validModel (g-i) (((pivot : ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I)) Y ≠ 0) :
    let ds₁ := (u : ℤ)::selected (d.map Int.ofNat) I
    let ds₂ := ((pivot : ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I)
    1 ≤ complexity i ds₁.length ∧ 1 ≤ complexity (g-i) ds₂.length ∧
      complexity i ds₁.length+complexity (g-i) ds₂.length+1=complexity g (d.length+1) := by
  have hs₁ := (validModel_ne_zero_support i _ Y hv₁).2.1
  have hs₂ := (validModel_ne_zero_support (g-i) _ Y hv₂).2.1
  have hlen := selected_partition_length (d.map Int.ofNat) I
  simp only [List.length_map] at hlen
  unfold Stable at hs₁ hs₂
  dsimp only
  simp only [List.length_cons] at hs₁ hs₂ ⊢
  unfold complexity
  omega

theorem weighted_recursion_upper_maxima (P : PsiTheory) (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (S : ℝ)
    (hg : 2 ≤ g) (hd : (pivot::d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀)
    (hsplit : ∀ j k : ℕ, 1 ≤ j → 1 ≤ k → j+k+1=complexity g (d.length+1) →
      clippedComplexityMaximum P c j*clippedComplexityMaximum P c k ≤ S*Real.exp ((1/12 : ℝ)*min j k)) :
    ratio P g (pivot::d) Y/clippedWeight c (pivot::d) ≤
      clippedComplexityMaximum P c (complexity g (d.length+1)-1)*weightedLinear c Y g pivot d+
        S*weightedSeparating c Y g pivot d := by
  apply weighted_recursion_upper P c Y g pivot d _ S hg hd hY
  · intro j hj l hl
    dsimp only
    intro hv
    have hj' := Finset.mem_range.mp hj
    have hn : 1 ≤ (((pivot : ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat).length := by simp
    have he := clippedRatio_le_maximum P c Y g _ hY hn hv
    rw [merger_child_rank g pivot d j l hg hj'] at he
    exact he
  · intro l hl u hu
    dsimp only
    intro hv
    have he := clippedRatio_le_maximum P c Y (g-1) _ hY (by simp) hv
    rw [contraction_child_rank g pivot d l u hg] at he
    exact he
  · intro l hl u hu i hi I hI
    dsimp only
    intro hv₁ hv₂
    have hc := separating_child_ranks g pivot d l u i I (by have := Finset.mem_range.mp hi; omega) Y hv₁ hv₂
    have h₁ := clippedRatio_le_maximum P c Y i _ hY (by simp) hv₁
    have h₂ := clippedRatio_le_maximum P c Y (g-i) _ hY (by simp) hv₂
    have hn₁ := clippedRatio_nonneg_of_validModel P c Y i _ hY (by simp) hv₁
    have hn₂ := clippedRatio_nonneg_of_validModel P c Y (g-i) _ hY (by simp) hv₂
    exact (mul_le_mul h₁ h₂ hn₂ (hn₁.trans h₁)).trans
      (hsplit _ _ hc.1 hc.2.1 hc.2.2)
lemma weightedLinear_nonneg (c Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hY : Y ∈ Set.Icc 0 y₀) : 0 ≤ weightedLinear c Y g pivot d := by
  have hM := (model_pos g (pivot::d) Y (by unfold Stable; simp only [List.length_cons]; omega) hY).le
  have hf (g' : ℕ) (ds : List ℤ) :
      0 ≤ validModel g' ds Y/model g (pivot::d) Y*signedWeight c ds/clippedWeight c (pivot::d) :=
    div_nonneg (mul_nonneg (div_nonneg (validModel_nonneg g' ds Y hY) hM) (signedWeight_pos c ds).le)
      (clippedWeight_pos c _).le
  have he := linearSum_mono Y g pivot d (fun _ _ => 0)
    (fun g' ds => validModel g' ds Y/model g (pivot::d) Y*signedWeight c ds/clippedWeight c (pivot::d)) hY
    (by intro j hj l hl; exact hf _ _) (by intro l hl u hu; exact hf _ _)
  rw [weightedLinear_eq_sum]
  simpa [linearSum] using he
lemma weightedSeparating_nonneg (c Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hY : Y ∈ Set.Icc 0 y₀) : 0 ≤ weightedSeparating c Y g pivot d := by
  have hM := (model_pos g (pivot::d) Y (by unfold Stable; simp only [List.length_cons]; omega) hY).le
  have hf (i j : ℕ) (ds₁ ds₂ : List ℤ) :
      0 ≤ validModel i ds₁ Y*validModel j ds₂ Y/model g (pivot::d) Y*
        signedWeight c ds₁*signedWeight c ds₂/clippedWeight c (pivot::d)*
          Real.exp ((1/12 : ℝ)*min (complexity i ds₁.length) (complexity j ds₂.length)) := by
    have hv₁ := validModel_nonneg i ds₁ Y hY
    have hv₂ := validModel_nonneg j ds₂ Y hY
    have hw₁ := (signedWeight_pos c ds₁).le
    have hw₂ := (signedWeight_pos c ds₂).le
    have hwp := (clippedWeight_pos c (pivot::d)).le
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hv₁ hv₂) hM) hw₁) hw₂) hwp)
      (Real.exp_pos _).le
  have he := separatingSum_mono Y g pivot d (fun _ _ _ _ => 0)
    (fun i ds₁ j ds₂ => validModel i ds₁ Y*validModel j ds₂ Y/model g (pivot::d) Y*
      signedWeight c ds₁*signedWeight c ds₂/clippedWeight c (pivot::d)*
        Real.exp ((1/12 : ℝ)*min (complexity i ds₁.length) (complexity j ds₂.length))) hY
    (by intro l hl u hu i hi I hI; exact hf _ _ _ _)
  rw [weightedSeparating_eq_sum]
  simpa [separatingSum] using he
lemma weighted_parent_at_exponential_record (P : PsiTheory) (c Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hd : (pivot::d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀)
    (a b C : ℝ) (hb : 0 < b) (hab : a-b ≤ (1/12 : ℝ)) (hC : 0 ≤ C)
    (hglobal : ∀ j : ℕ, clippedComplexityMaximum P c j ≤ C*Real.exp (a*j))
    (hrec : ∀ j : ℕ, j < complexity g (d.length+1) →
      clippedComplexityMaximum P c j*Real.exp (-b*j) ≤
        clippedComplexityMaximum P c (complexity g (d.length+1))*Real.exp (-b*complexity g (d.length+1))) :
    ratio P g (pivot::d) Y/clippedWeight c (pivot::d) ≤
      clippedComplexityMaximum P c (complexity g (d.length+1))*
        (Real.exp (-b)*weightedLinear c Y g pivot d+C*weightedSeparating c Y g pivot d) := by
  let f := clippedComplexityMaximum P c
  let h := complexity g (d.length+1)
  have hpos := clippedComplexityMaximum_nonneg P c
  have hh : 1 ≤ h := by dsimp only [h]; unfold complexity; omega
  have hsplit (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hrank : j+k+1=h) :
      f j*f k ≤ (f h*C)*Real.exp ((1/12 : ℝ)*min j k) := by
    rcases le_total j k with hjk | hkj
    · have he := Analysis.record_split_exponential_bound f hpos a b (1/12) C hb hab hC hglobal h hrec j k hrank
      simpa only [Nat.min_eq_left hjk] using he
    · have he := Analysis.record_split_exponential_bound f hpos a b (1/12) C hb hab hC hglobal h hrec k j (by omega)
      simpa only [Nat.min_eq_right hkj,mul_comm] using he
  have he := weighted_recursion_upper_maxima P c Y g pivot d (f h*C) hg hd hY hsplit
  have hprev := Analysis.value_le_record_exponential f (fun j => b*j) h (by
    intro j hj
    simpa only [neg_mul] using hrec j hj) (h-1) (by omega)
  have hcast : ((h-1 : ℕ) : ℝ)=(h : ℝ)-1 := by rw [Nat.cast_sub hh]; norm_num
  have harg : b*(h-1 : ℕ)-b*h = -b := by rw [hcast]; ring
  rw [harg] at hprev
  apply he.trans
  have hm := mul_le_mul_of_nonneg_right hprev (weightedLinear_nonneg c Y g pivot d hg hY)
  calc
    _ ≤ (f h*Real.exp (-b))*weightedLinear c Y g pivot d+(f h*C)*weightedSeparating c Y g pivot d :=
      add_le_add_left hm _
    _ = _ := by ring
lemma weighted_parent_at_monotone_record (P : PsiTheory) (c Y : ℝ) (g pivot : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hd : (pivot::d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀)
    (q : ℕ → ℝ) (hq : Monotone q) (a C : ℝ) (ha : a ≤ (1/12 : ℝ)) (hC : 0 ≤ C)
    (hglobal : ∀ j : ℕ, clippedComplexityMaximum P c j ≤ C*Real.exp (a*j))
    (hrec : ∀ j : ℕ, j < complexity g (d.length+1) →
      clippedComplexityMaximum P c j*Real.exp (-q j) ≤
        clippedComplexityMaximum P c (complexity g (d.length+1))*Real.exp (-q (complexity g (d.length+1)))) :
    ratio P g (pivot::d) Y/clippedWeight c (pivot::d) ≤
      clippedComplexityMaximum P c (complexity g (d.length+1))*
        (Real.exp (q (complexity g (d.length+1)-1)-q (complexity g (d.length+1)))*weightedLinear c Y g pivot d+
          C*weightedSeparating c Y g pivot d) := by
  let f := clippedComplexityMaximum P c
  let h := complexity g (d.length+1)
  have hpos := clippedComplexityMaximum_nonneg P c
  have hh : 1 ≤ h := by dsimp only [h]; unfold complexity; omega
  have hsplit (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hrank : j+k+1=h) :
      f j*f k ≤ (f h*C)*Real.exp ((1/12 : ℝ)*min j k) := by
    rcases le_total j k with hjk | hkj
    · have he := Analysis.record_split_monotone_bound f hpos q hq a (1/12) C ha hC hglobal h hrec j k hrank
      simpa only [Nat.min_eq_left hjk] using he
    · have he := Analysis.record_split_monotone_bound f hpos q hq a (1/12) C ha hC hglobal h hrec k j (by omega)
      simpa only [Nat.min_eq_right hkj,mul_comm] using he
  have he := weighted_recursion_upper_maxima P c Y g pivot d (f h*C) hg hd hY hsplit
  have hprev := Analysis.value_le_record_exponential f q h hrec (h-1) (by omega)
  apply he.trans
  have hm := mul_le_mul_of_nonneg_right hprev (weightedLinear_nonneg c Y g pivot d hg hY)
  calc
    _ ≤ (f h*Real.exp (q (h-1)-q h))*weightedLinear c Y g pivot d+(f h*C)*weightedSeparating c Y g pivot d :=
      add_le_add_left hm _
    _ = _ := by ring
lemma clippedMaximum_pivot_attained (P : PsiTheory) (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ g pivot : ℕ, ∃ d : List ℕ, PivotChoice pivot d ∧ Stable g (d.length+1) ∧
      (pivot::d).sum ≤ dimension g (d.length+1) ∧ complexity g (d.length+1)=n ∧
        ∃ Y ∈ Set.Icc 0 y₀, clippedComplexityMaximum P c n=ratio P g (pivot::d) Y/clippedWeight c (pivot::d) := by
  obtain ⟨g,ds,hn',hs,hd,hr,Y,hY,hmax⟩ := clippedComplexityMaximum_attained P c n hn
  obtain ⟨pivot,d,hp,hchoice⟩ := exists_pivot_choice ds hn'
  have hlen : ds.length=d.length+1 := by simpa only [List.length_cons] using hp.length_eq
  refine ⟨g,pivot,d,hchoice,?_,?_,?_,Y,hY,?_⟩
  · simpa only [hlen] using hs
  · simpa only [hp.sum_eq,hlen] using hd
  · simpa only [hlen] using hr
  · rw [hmax,ratio_perm P g hp Y,clippedWeight_perm c hp]
lemma exponential_record_recurrence (P : PsiTheory) (c L B K a b C : ℝ)
    (hb : 0 < b) (hab : a-b ≤ (1/12 : ℝ)) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hglobal : ∀ j : ℕ, clippedComplexityMaximum P c j ≤ C*Real.exp (a*j))
    (hterminal : ∀ g : ℕ, ∀ ds : List ℕ, 1 ≤ ds.length → Stable g ds.length →
      ds.sum ≤ dimension g ds.length → Terminal g ds → ∀ Y ∈ Set.Icc 0 y₀,
        ratio P g ds Y/clippedWeight c ds ≤ K)
    (hlinear : ∀ g pivot : ℕ, ∀ d : List ℕ, PivotChoice pivot d → ¬ Terminal g (pivot::d) →
      (pivot::d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedLinear c Y g pivot d ≤ 1+L/Real.sqrt (complexity g (d.length+1)))
    (hseparating : ∀ g pivot : ℕ, ∀ d : List ℕ, PivotChoice pivot d → ¬ Terminal g (pivot::d) →
      (pivot::d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedSeparating c Y g pivot d ≤ B/Real.sqrt (complexity g (d.length+1)))
    (n : ℕ) (hn : 2 ≤ n)
    (hrec : ∀ j : ℕ, j<n → clippedComplexityMaximum P c j*Real.exp (-b*j) ≤
      clippedComplexityMaximum P c n*Real.exp (-b*n)) :
    clippedComplexityMaximum P c n*Real.exp (-b*n) ≤ K ∨
      1 ≤ (1+L/Real.sqrt n)*Real.exp (-b)+(C*B)/Real.sqrt n := by
  let f := clippedComplexityMaximum P c
  change f n*Real.exp (-b*n) ≤ K ∨ _
  by_cases hfn : 0 < f n
  · obtain ⟨g,pivot,d,hchoice,hs,hd,hrank,Y,hY,hmax⟩ := clippedMaximum_pivot_attained P c n (by omega)
    change f n=ratio P g (pivot::d) Y/clippedWeight c (pivot::d) at hmax
    by_cases ht : Terminal g (pivot::d)
    · left
      have hT : f n ≤ K := by
        rw [hmax]
        exact hterminal g (pivot::d) (by simp) (by simpa only [List.length_cons] using hs)
          (by simpa only [List.length_cons] using hd) ht Y hY
      have hE : Real.exp (-b*n) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg n))
      have hscaled : f n*Real.exp (-b*n) ≤ f n := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hE hfn.le
      exact hscaled.trans hT
    · right
      have hg : 2 ≤ g := by unfold Terminal at ht; omega
      have he := weighted_parent_at_exponential_record P c Y g pivot d hg hd hY a b C hb hab hC hglobal
        (by simpa only [hrank] using hrec)
      rw [hrank,← hmax] at he
      have hfactor : 1 ≤ Real.exp (-b)*weightedLinear c Y g pivot d+C*weightedSeparating c Y g pivot d := by
        exact (mul_le_mul_iff_right₀ hfn).mp (by simpa only [mul_one] using he)
      have hl := hlinear g pivot d hchoice ht hd Y hY
      have hs := hseparating g pivot d hchoice ht hd Y hY
      rw [hrank] at hl hs
      apply hfactor.trans
      have h₁ := mul_le_mul_of_nonneg_left hl (Real.exp_pos (-b)).le
      have h₂ := mul_le_mul_of_nonneg_left hs hC
      convert add_le_add h₁ h₂ using 1 <;> ring
  · left
    have hz : f n=0 := by have hp := clippedComplexityMaximum_nonneg P c n; change 0 ≤ f n at hp; linarith
    rw [hz,zero_mul]
    exact hK
lemma sqrt_record_recurrence (P : PsiTheory) (c L B K a C : ℝ)
    (ha : a ≤ (1/12 : ℝ)) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hglobal : ∀ j : ℕ, clippedComplexityMaximum P c j ≤ C*Real.exp (a*j))
    (hterminal : ∀ g : ℕ, ∀ ds : List ℕ, 1 ≤ ds.length → Stable g ds.length →
      ds.sum ≤ dimension g ds.length → Terminal g ds → ∀ Y ∈ Set.Icc 0 y₀,
        ratio P g ds Y/clippedWeight c ds ≤ K)
    (hlinear : ∀ g pivot : ℕ, ∀ d : List ℕ, PivotChoice pivot d → ¬ Terminal g (pivot::d) →
      (pivot::d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedLinear c Y g pivot d ≤ 1+L/Real.sqrt (complexity g (d.length+1)))
    (hseparating : ∀ g pivot : ℕ, ∀ d : List ℕ, PivotChoice pivot d → ¬ Terminal g (pivot::d) →
      (pivot::d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedSeparating c Y g pivot d ≤ B/Real.sqrt (complexity g (d.length+1)))
    (A : ℝ) (hA : 0 < A) (n : ℕ) (hn : 2 ≤ n)
    (hrec : ∀ j : ℕ, j<n → clippedComplexityMaximum P c j*Real.exp (-A*Real.sqrt j) ≤
      clippedComplexityMaximum P c n*Real.exp (-A*Real.sqrt n)) :
    clippedComplexityMaximum P c n*Real.exp (-A*Real.sqrt n) ≤ K ∨
      1 ≤ (1+L/Real.sqrt n)*Real.exp (A*(Real.sqrt (n-1 : ℕ)-Real.sqrt n))+(C*B)/Real.sqrt n := by
  let f := clippedComplexityMaximum P c
  change f n*Real.exp (-A*Real.sqrt n) ≤ K ∨ _
  let q := fun j : ℕ => A*Real.sqrt j
  have hq : Monotone q := by
    intro j k hjk
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hjk)) hA.le
  by_cases hfn : 0 < f n
  · obtain ⟨g,pivot,d,hchoice,hs,hd,hrank,Y,hY,hmax⟩ := clippedMaximum_pivot_attained P c n (by omega)
    change f n=ratio P g (pivot::d) Y/clippedWeight c (pivot::d) at hmax
    by_cases ht : Terminal g (pivot::d)
    · left
      have hT : f n ≤ K := by
        rw [hmax]
        exact hterminal g (pivot::d) (by simp) (by simpa only [List.length_cons] using hs)
          (by simpa only [List.length_cons] using hd) ht Y hY
      have hE : Real.exp (-A*Real.sqrt n) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA.le) (Real.sqrt_nonneg _))
      have hscaled : f n*Real.exp (-A*Real.sqrt n) ≤ f n := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hE hfn.le
      exact hscaled.trans hT
    · right
      have hg : 2 ≤ g := by unfold Terminal at ht; omega
      have he := weighted_parent_at_monotone_record P c Y g pivot d hg hd hY q hq a C ha hC hglobal
        (by simpa only [q,hrank,neg_mul] using hrec)
      rw [hrank,← hmax] at he
      have harg : q (n-1)-q n=A*(Real.sqrt (n-1 : ℕ)-Real.sqrt n) := by dsimp only [q]; ring
      rw [harg] at he
      have hfactor : 1 ≤ Real.exp (A*(Real.sqrt (n-1 : ℕ)-Real.sqrt n))*weightedLinear c Y g pivot d+
          C*weightedSeparating c Y g pivot d := by
        exact (mul_le_mul_iff_right₀ hfn).mp (by simpa only [mul_one] using he)
      have hl := hlinear g pivot d hchoice ht hd Y hY
      have hs := hseparating g pivot d hchoice ht hd Y hY
      rw [hrank] at hl hs
      apply hfactor.trans
      have h₁ := mul_le_mul_of_nonneg_left hl (Real.exp_pos (A*(Real.sqrt (n-1 : ℕ)-Real.sqrt n))).le
      have h₂ := mul_le_mul_of_nonneg_left hs hC
      convert add_le_add h₁ h₂ using 1 <;> ring
  · left
    have hz : f n=0 := by have hp := clippedComplexityMaximum_nonneg P c n; change 0 ≤ f n at hp; linarith
    rw [hz,zero_mul]
    exact hK
end WP.Comparison
