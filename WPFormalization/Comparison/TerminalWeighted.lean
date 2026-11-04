import WPFormalization.Weighted.Clipping
import WPFormalization.Analysis.TerminalUpper
import WPFormalization.Intersection.TerminalLower
/-! The actual terminal ratios divided by the actual clipped weight are
uniformly bounded for every fixed positive clipping parameter. The dimension
boundary uses the exact pure normalization; low genera use inactive-count
bookkeeping and the exponential-series bound for powers over a factorial.
No terminal weighted bound or new analytic estimate is assumed. -/
noncomputable section
open Set
namespace WP

lemma pow_div_sqrt_factorial_le_exp_sq (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    a^n / Real.sqrt (n.factorial:ℝ) ≤ Real.exp (a^2) := by
  have hs : (a^n / Real.sqrt (n.factorial:ℝ))^2 = (a^2)^n/(n.factorial:ℝ) := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  have hb := Real.pow_div_factorial_le_exp (a^2) (sq_nonneg a) n
  have he := Real.one_le_exp (sq_nonneg a)
  have hx : 0 ≤ a^n / Real.sqrt (n.factorial:ℝ) := by positivity
  rw [← hs] at hb
  nlinarith

lemma length_le_sum_add_twice_inactive (d : List ℕ) :
    2*d.length ≤ d.sum+2*inactive d := by
  induction d with
  | nil => simp [inactive]
  | cons a d ih =>
    by_cases ha : a ≤ 1
    · have hi : inactive (a::d) = inactive d+1 := by simp [inactive,ha]
      simp only [List.length_cons,List.sum_cons,hi]
      omega
    · have hi : inactive (a::d) = inactive d := by simp [inactive,ha]
      simp only [List.length_cons,List.sum_cons,hi]
      omega

lemma small_genus_complexity_le_twice_inactive (g : ℕ) (d : List ℕ)
    (hg : g ≤ 1) (hd : d.sum ≤ dimension g d.length) :
    complexity g d.length ≤ 2*inactive d := by
  have hh : complexity g d.length ≤ d.length := by unfold complexity;omega
  have hdim : dimension g d.length ≤ d.length := by unfold dimension;omega
  have hi := length_le_sum_add_twice_inactive d
  omega

lemma rawPhi_le_clippedWeight (c : ℝ) (hc : 0 ≤ c) (d : List ℕ) :
    rawPhi c (inactive d) ≤ clippedWeight c d := by
  rw [clippedWeight_phi]
  exact (rawPhi_le_clippedPhi c hc _).trans
    (le_mul_of_one_le_left (clippedPhi_pos c _).le (one_le_pow₀ (by norm_num)))

lemma exp_complexity_div_weight_small_genus (c : ℝ) (hc : 0 < c)
    (C : ℝ) (hC : 0 ≤ C) (g : ℕ) (d : List ℕ) (hg : g ≤ 1)
    (hd : d.sum ≤ dimension g d.length) :
    Real.exp (C*complexity g d.length) / clippedWeight c d ≤
      Real.exp ((Real.exp (2*C)/c)^2) := by
  have hh := small_genus_complexity_le_twice_inactive g d hg hd
  have hhR : (complexity g d.length:ℝ) ≤ 2*(inactive d:ℝ) := by exact_mod_cast hh
  calc
    _ ≤ Real.exp (2*C*(inactive d:ℝ)) / clippedWeight c d := by
      apply div_le_div_of_nonneg_right _ (clippedWeight_pos c d).le
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ Real.exp (2*C*(inactive d:ℝ)) / rawPhi c (inactive d) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (rawPhi_pos c hc _)
        (rawPhi_le_clippedWeight c hc.le d)
    _ = (Real.exp (2*C)/c)^(inactive d) / Real.sqrt ((inactive d).factorial:ℝ) := by
      rw [mul_comm (2*C) (inactive d:ℝ),Real.exp_nat_mul]
      simp only [rawPhi,div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := pow_div_sqrt_factorial_le_exp_sq _ (div_nonneg (Real.exp_pos _).le hc.le) _

lemma ratio_top_eq_pureC (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hd : d.sum = dimension g d.length)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : ratio P g d Y = pureC P g d := by
  have hm : deficit g d = 0 := by simp [deficit,hd]
  have hcoef : harmonicCoeff Y (complexity g d.length) 0 = 1 := by
    simp [harmonicCoeff,realCoeff,coeff,barH_zero Y hY]
  unfold ratio model
  rw [hm,hcoef,normalized_top P g d Y hY hd]
  simp only [weighted,doubleWeight,pure,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,mul_one]
  unfold pureC pure
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

lemma pureC_div_clippedWeight_le_one (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hd : d.sum = dimension g d.length)
    (c : ℝ) : pureC P g d / clippedWeight c d ≤ 1 := by
  apply (div_le_one (clippedWeight_pos c d)).2
  have hcnt : d.count 0 = zeros d := by simp only [zeros,←count_zero_filter_length]
  calc
    _ ≤ (2:ℝ)^(zeros d) := by simpa only [hcnt] using (pureC_zero_bounds P g d hs hd).2
    _ ≤ (4:ℝ)^(zeros d) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ ≤ clippedWeight c d := by
      rw [clippedWeight_phi]
      exact le_mul_of_one_le_right (by positivity) (clippedPhi_ge_one c _)

lemma terminal_weighted_ratio_bounded (P : PsiTheory) (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : ℕ, ∀ d : List ℕ,
      1 ≤ d.length → Stable g d.length → d.sum ≤ dimension g d.length →
      Terminal g d → ∀ Y ∈ Icc (0:ℝ) y₀,
        ratio P g d Y / clippedWeight c d ≤ K := by
  obtain ⟨C,hC,hUpper⟩ := Analysis.ratio_uniform_global_upper P
  refine ⟨Real.exp ((Real.exp (2*C)/c)^2),Real.exp_pos _,?_⟩
  intro g d hn hs hd ht Y hY
  rcases ht with hm | hg
  · have htop : d.sum = dimension g d.length := by unfold deficit at hm;omega
    rw [ratio_top_eq_pureC P g d hs htop Y hY]
    exact (pureC_div_clippedWeight_le_one P g d hs htop c).trans
      (Real.one_le_exp (sq_nonneg _))
  · calc
      _ ≤ Real.exp (C*complexity g d.length) / clippedWeight c d :=
        div_le_div_of_nonneg_right (hUpper g d hs hd Y hY) (clippedWeight_pos c d).le
      _ ≤ _ := exp_complexity_div_weight_small_genus c hc C hC.le g d hg hd
end WP
