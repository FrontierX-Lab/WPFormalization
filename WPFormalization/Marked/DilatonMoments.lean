import WPFormalization.Marked.RatioBounds
/-! Exact sums and uniform absolute polynomial moments of the canonical dilaton coefficients.
The estimates use Cauchy bounds for the actual entire H kernel on radius two. -/
noncomputable section
namespace WP
open Set Filter
lemma canonicalDilatonCoefficient_succ_hasSum (Y : ℝ) :
    HasSum (fun n => canonicalDilatonCoefficient Y (n+1)) (A Y) := by
  have hs := Complex.hasSum_taylorSeries_of_entire (barH_differentiable Y) 0 1
  have hsc : HasSum (fun n => coeff (barH Y) n) (barH Y 1) := by
    convert! hs using 1
    ext n
    simp only [coeff,sub_zero,one_pow,smul_eq_mul,mul_one]
    ring
  have hr : HasSum (fun n => realCoeff (barH Y) n) (barH Y 1).re := by
    simpa only [realCoeff,Complex.reCLM_apply] using hsc.mapL Complex.reCLM
  convert! hr.div_const 3 using 1 <;> simp [canonicalDilatonCoefficient,A]
lemma canonicalDilatonCoefficient_hasSum (Y : ℝ) : HasSum (canonicalDilatonCoefficient Y) (A Y) := by
  have hs := (hasSum_nat_add_iff (f := canonicalDilatonCoefficient Y) 1).mp
    (canonicalDilatonCoefficient_succ_hasSum Y)
  have hzero : canonicalDilatonCoefficient Y 0=0 := by simp [canonicalDilatonCoefficient]
  simpa only [Finset.sum_range_one,hzero,add_zero] using hs
lemma barH_radius_two_coefficient_bound : ∃ B : ℝ, 0 < B ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ n : ℕ, |realCoeff (barH Y) n| ≤ B/2^n := by
  have hc : Continuous (fun p : Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) 2 => barH (p.1:ℝ) p.2) :=
    Analysis.barH_joint_continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨M,hM⟩ := isCompact_univ.bddAbove_image hc.norm.continuousOn
  let B := max M 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨B,hB,?_⟩
  intro Y hY n
  have hcircle : ∀ z ∈ Metric.sphere (0:ℂ) 2, ‖barH Y z‖ ≤ B := by
    intro z hz
    have hz' := Metric.sphere_subset_closedBall hz
    exact (hM (mem_image_of_mem _
      (show (⟨Y,hY⟩,⟨z,hz'⟩) ∈ (univ : Set (Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) 2)) from mem_univ _))).trans
      (le_max_left _ _)
  exact (Complex.abs_re_le_norm _).trans
    (Analysis.coeff_norm_le_circle_bound (barH Y) 2 B (by norm_num)
      (barH_differentiable Y).differentiableOn hcircle n)
lemma summable_half_geometric_quadratic : Summable (fun n : ℕ => ((n : ℝ)+2)^2*(1/2 : ℝ)^n) := by
  have hs := (summable_nat_add_iff 2).mpr
    (summable_pow_mul_geometric_of_norm_lt_one 2 (r := (1/2 : ℝ)) (by norm_num))
  have ht := hs.mul_left 4
  apply ht.congr
  intro n
  simp only [Nat.cast_add,Nat.cast_ofNat,pow_add]
  norm_num only [show (1/2 : ℝ)^2=1/4 by norm_num]
  ring
lemma sum_half_geometric_quadratic_bound : ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ,
    (∑ n ∈ Finset.range N, ((n : ℝ)+2)^2*(1/2 : ℝ)^n) ≤ D := by
  let D := 1+∑' n : ℕ, ((n : ℝ)+2)^2*(1/2 : ℝ)^n
  have hsum : 0 ≤ ∑' n : ℕ, ((n : ℝ)+2)^2*(1/2 : ℝ)^n := tsum_nonneg (by intro n; positivity)
  refine ⟨D,by dsimp only [D]; positivity,?_⟩
  intro N
  exact (Summable.sum_le_tsum (Finset.range N) (by intro n hn; positivity)
    summable_half_geometric_quadratic).trans (by dsimp only [D]; linarith)
lemma canonicalDilatonCoefficient_succ_quadratic_abs_sum_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ N : ℕ,
      (∑ n ∈ Finset.range N, ((n : ℝ)+2)^2*|canonicalDilatonCoefficient Y (n+1)|) ≤ C := by
  obtain ⟨B,hB,hcoeff⟩ := barH_radius_two_coefficient_bound
  obtain ⟨D,hD,hbound⟩ := sum_half_geometric_quadratic_bound
  refine ⟨(B/3)*D,by positivity,?_⟩
  intro Y hY N
  calc
    _ ≤ ∑ n ∈ Finset.range N, (B/3)*(((n : ℝ)+2)^2*(1/2 : ℝ)^n) := by
      apply Finset.sum_le_sum
      intro n hn
      have he := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hcoeff Y hY n) (by norm_num : (0:ℝ)≤3)) (sq_nonneg ((n : ℝ)+2))
      simp only [canonicalDilatonCoefficient,show 1≤n+1 by omega,ite_true,Nat.add_sub_cancel,
        abs_div,abs_of_pos (by norm_num : (0:ℝ)<3)]
      apply he.trans_eq
      rw [div_pow,one_pow]
      ring
    _ = (B/3)*(∑ n ∈ Finset.range N, ((n : ℝ)+2)^2*(1/2 : ℝ)^n) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound N) (by positivity)
lemma canonicalDilatonCoefficient_quadratic_abs_sum_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ N : ℕ,
      (∑ d ∈ Finset.range N, ((d : ℝ)+1)^2*|canonicalDilatonCoefficient Y d|) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := canonicalDilatonCoefficient_succ_quadratic_abs_sum_uniform
  refine ⟨C,hC,?_⟩
  intro Y hY N
  cases N with
  | zero => simpa using hC.le
  | succ N =>
    rw [Finset.sum_range_succ']
    have hzero : canonicalDilatonCoefficient Y 0=0 := by simp [canonicalDilatonCoefficient]
    simp only [hzero,abs_zero,mul_zero,add_zero]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1 : ℝ)+1=2 by norm_num] using hbound Y hY N
lemma summable_half_geometric_moment (q : ℕ) :
    Summable (fun n : ℕ => ((n:ℝ)+2)^q*(1/2:ℝ)^n) := by
  have hs := (summable_nat_add_iff 2).mpr
    (summable_pow_mul_geometric_of_norm_lt_one q (r := (1/2:ℝ)) (by norm_num))
  have ht := hs.mul_left 4
  apply ht.congr
  intro n
  simp only [Nat.cast_add,Nat.cast_ofNat,pow_add]
  norm_num only [show (1/2:ℝ)^2=1/4 by norm_num]
  ring
lemma sum_half_geometric_moment_bound (q : ℕ) : ∃ D : ℝ, 0<D ∧ ∀ N : ℕ,
    (∑ n ∈ Finset.range N, ((n:ℝ)+2)^q*(1/2:ℝ)^n) ≤ D := by
  let D := 1+∑' n : ℕ, ((n:ℝ)+2)^q*(1/2:ℝ)^n
  have hsum : 0≤∑' n : ℕ, ((n:ℝ)+2)^q*(1/2:ℝ)^n := tsum_nonneg (by intro n;positivity)
  refine ⟨D,by dsimp only [D];positivity,?_⟩
  intro N
  exact (Summable.sum_le_tsum (Finset.range N) (by intro n hn;positivity)
    (summable_half_geometric_moment q)).trans (by dsimp only [D];linarith)
lemma canonicalDilatonCoefficient_succ_moment_pointwise (q : ℕ) : ∃ B : ℝ, 0<B ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ n : ℕ,
      ((n:ℝ)+2)^q*|canonicalDilatonCoefficient Y (n+1)| ≤
        (B/3)*(((n:ℝ)+2)^q*(1/2:ℝ)^n) := by
  obtain ⟨B,hB,hcoeff⟩ := barH_radius_two_coefficient_bound
  refine ⟨B,hB,?_⟩
  intro Y hY n
  have he := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (hcoeff Y hY n) (by norm_num : (0:ℝ)≤3))
    (show 0≤((n:ℝ)+2)^q by positivity)
  simp only [canonicalDilatonCoefficient,show 1≤n+1 by omega,ite_true,Nat.add_sub_cancel,
    abs_div,abs_of_pos (by norm_num : (0:ℝ)<3)]
  apply he.trans_eq
  rw [div_pow,one_pow]
  ring
lemma canonicalDilatonCoefficient_succ_moment_abs_sum_uniform (q : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ N : ℕ,
      (∑ n ∈ Finset.range N, ((n:ℝ)+2)^q*|canonicalDilatonCoefficient Y (n+1)|) ≤ C := by
  obtain ⟨B,hB,hpoint⟩ := canonicalDilatonCoefficient_succ_moment_pointwise q
  obtain ⟨D,hD,hbound⟩ := sum_half_geometric_moment_bound q
  refine ⟨(B/3)*D,by positivity,?_⟩
  intro Y hY N
  calc _ ≤ ∑ n ∈ Finset.range N, (B/3)*(((n:ℝ)+2)^q*(1/2:ℝ)^n) :=
          Finset.sum_le_sum (fun n hn => hpoint Y hY n)
       _ = (B/3)*(∑ n ∈ Finset.range N, ((n:ℝ)+2)^q*(1/2:ℝ)^n) :=
         (Finset.mul_sum _ _ _).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (hbound N) (by positivity)
lemma canonicalDilatonCoefficient_moment_abs_sum_uniform (q : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, ∀ N : ℕ,
      (∑ d ∈ Finset.range N, ((d:ℝ)+1)^q*|canonicalDilatonCoefficient Y d|) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := canonicalDilatonCoefficient_succ_moment_abs_sum_uniform q
  refine ⟨C,hC,?_⟩
  intro Y hY N
  cases N with
  | zero => simpa using hC.le
  | succ N =>
    rw [Finset.sum_range_succ']
    have hzero : canonicalDilatonCoefficient Y 0=0 := by simp [canonicalDilatonCoefficient]
    simp only [hzero,abs_zero,mul_zero,add_zero]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hbound Y hY N
lemma canonicalDilatonCoefficient_moment_summable (q : ℕ) (Y : ℝ) (hY : Y ∈ Icc (0:ℝ) y₀) :
    Summable (fun d : ℕ => ((d:ℝ)+1)^q*|canonicalDilatonCoefficient Y d|) := by
  obtain ⟨B,hB,hpoint⟩ := canonicalDilatonCoefficient_succ_moment_pointwise q
  have hs := (summable_half_geometric_moment q).mul_left (B/3)
  have ht : Summable (fun n : ℕ => ((n:ℝ)+2)^q*|canonicalDilatonCoefficient Y (n+1)|) :=
    Summable.of_nonneg_of_le (by intro n;positivity) (hpoint Y hY) hs
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using ht
lemma canonicalDilatonCoefficient_moment_tsum_uniform (q : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ Y ∈ Icc (0:ℝ) y₀,
      (∑' d : ℕ, ((d:ℝ)+1)^q*|canonicalDilatonCoefficient Y d|) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := canonicalDilatonCoefficient_moment_abs_sum_uniform q
  refine ⟨C,hC,?_⟩
  intro Y hY
  exact le_of_tendsto (canonicalDilatonCoefficient_moment_summable q Y hY).hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall (hbound Y hY))
end WP
