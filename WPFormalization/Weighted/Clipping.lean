import WPFormalization.Statements.Comparison
/-! The actual clipped factorial weight in (5.8), its uniform factorial
comparison for each positive clipping parameter, and the inverse square-root
binomial envelope for genuine labeled partitions. No weighted recursion bound
is assumed; every result here uses only finite products, count identities, and
real square roots. -/
noncomputable section
namespace WP
/-- The genuine clipped factorial factor of (5.8). -/
def clippedPhi (c : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, max 1 (c*Real.sqrt (j+1))
def rawPhi (c : ℝ) (n : ℕ) : ℝ := c^n*Real.sqrt (n.factorial)
lemma clippedWeight_phi (c : ℝ) (d : List ℕ) :
    clippedWeight c d = (4 : ℝ)^(zeros d)*clippedPhi c (inactive d) := rfl
lemma clippedPhi_succ (c : ℝ) (n : ℕ) :
    clippedPhi c (n+1) = clippedPhi c n*max 1 (c*Real.sqrt (n+1)) := by
  exact Finset.prod_range_succ _ _
lemma clippedPhi_ge_one (c : ℝ) (n : ℕ) : 1 ≤ clippedPhi c n := by
  apply Finset.one_le_prod₀
  intro j hj
  exact le_max_left _ _
lemma clippedPhi_pos (c : ℝ) (n : ℕ) : 0 < clippedPhi c n :=
  lt_of_lt_of_le (by norm_num) (clippedPhi_ge_one c n)
lemma clippedPhi_mono (c : ℝ) : Monotone (clippedPhi c) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [clippedPhi_succ]
  exact le_mul_of_one_le_right (clippedPhi_pos c n).le (le_max_left _ _)
lemma clippingFactor_mono (c : ℝ) (hc : 0 ≤ c) :
    Monotone (fun n : ℕ => max 1 (c*Real.sqrt (n+1))) := by
  intro i j hij
  apply max_le_max le_rfl
  apply mul_le_mul_of_nonneg_left _ hc
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.add_le_add_right hij 1
lemma clippedPhi_supermultiplicative (c : ℝ) (hc : 0 ≤ c) (a b : ℕ) :
    clippedPhi c a*clippedPhi c b ≤ clippedPhi c (a+b) := by
  unfold clippedPhi
  rw [Finset.prod_range_add]
  apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) (clippedPhi_ge_one c a))
  apply Finset.prod_le_prod₀
  · intro j hj
    exact le_trans (by norm_num) (le_max_left _ _)
  · intro j hj
    exact clippingFactor_mono c hc (show j ≤ a+j by omega)
lemma rawPhi_succ (c : ℝ) (n : ℕ) :
    rawPhi c (n+1) = rawPhi c n*(c*Real.sqrt (n+1)) := by
  unfold rawPhi
  rw [Nat.factorial_succ,pow_succ,Nat.cast_mul,Real.sqrt_mul (by positivity)]
  push_cast
  ring
lemma rawPhi_pos (c : ℝ) (hc : 0 < c) (n : ℕ) : 0 < rawPhi c n := by
  unfold rawPhi
  exact mul_pos (pow_pos hc _) (Real.sqrt_pos_of_pos (by positivity))
lemma rawPhi_le_clippedPhi (c : ℝ) (hc : 0 ≤ c) (n : ℕ) : rawPhi c n ≤ clippedPhi c n := by
  induction n with
  | zero => simp [rawPhi,clippedPhi]
  | succ n ih =>
    rw [rawPhi_succ,clippedPhi_succ]
    exact mul_le_mul ih (le_max_right _ _) (by positivity) (clippedPhi_pos c n).le
def clippedRatio (c : ℝ) (n : ℕ) : ℝ := clippedPhi c n/rawPhi c n
lemma clippedRatio_pos (c : ℝ) (hc : 0 < c) (n : ℕ) : 0 < clippedRatio c n :=
  div_pos (clippedPhi_pos c n) (rawPhi_pos c hc n)
lemma clippedRatio_succ (c : ℝ) (hc : 0 < c) (n : ℕ) :
    clippedRatio c (n+1) = clippedRatio c n*
      (max 1 (c*Real.sqrt (n+1))/(c*Real.sqrt (n+1))) := by
  unfold clippedRatio
  rw [clippedPhi_succ,rawPhi_succ]
  ring
lemma clippedRatio_mono (c : ℝ) (hc : 0 < c) : Monotone (clippedRatio c) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [clippedRatio_succ c hc]
  apply le_mul_of_one_le_right (clippedRatio_pos c hc n).le
  have hx : 0 < c*Real.sqrt (n+1) := by positivity
  exact (one_le_div hx).mpr (le_max_right _ _)
lemma clipping_eventually_inactive (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → 1 ≤ c*Real.sqrt (j+1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (c⁻¹^2)
  refine ⟨N,?_⟩
  intro j hj
  have hjR : (N : ℝ) ≤ j := by exact_mod_cast hj
  have hInv : 0 < c⁻¹ := inv_pos.mpr hc
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ j+1 by positivity)
  have hsqrt := Real.sqrt_nonneg ((j : ℝ)+1)
  have hh : c⁻¹ ≤ Real.sqrt (j+1) := by nlinarith
  calc
    (1 : ℝ) = c*c⁻¹ := by rw [mul_inv_cancel₀ hc.ne']
    _ ≤ c*Real.sqrt (j+1) := mul_le_mul_of_nonneg_left hh hc.le
lemma clippedRatio_stable (c : ℝ) (hc : 0 < c) (N : ℕ)
    (hN : ∀ j : ℕ, N ≤ j → 1 ≤ c*Real.sqrt (j+1)) (n : ℕ) (hn : N ≤ n) :
    clippedRatio c n = clippedRatio c N := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [clippedRatio_succ c hc,max_eq_right (hN n hn),div_self (by positivity),mul_one,ih]
lemma clippedPhi_factorial_comparison (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      c^n*Real.sqrt (n.factorial) ≤ clippedPhi c n ∧
      clippedPhi c n ≤ C*c^n*Real.sqrt (n.factorial) := by
  obtain ⟨N,hN⟩ := clipping_eventually_inactive c hc
  refine ⟨clippedRatio c N,clippedRatio_pos c hc N,?_⟩
  intro n
  refine ⟨rawPhi_le_clippedPhi c hc.le n,?_⟩
  have hr : clippedRatio c n ≤ clippedRatio c N := by
    rcases le_total n N with hn | hn
    · exact clippedRatio_mono c hc hn
    · exact (clippedRatio_stable c hc N hN n hn).le
  have he := (div_le_iff₀ (rawPhi_pos c hc n)).mp hr
  simpa only [rawPhi,mul_assoc] using he
lemma rawPhi_binomial_ratio (c : ℝ) (hc : 0 < c) (a b : ℕ) :
    rawPhi c a*rawPhi c b/rawPhi c (a+b) =
      1/Real.sqrt (Nat.choose (a+b) a) := by
  have hC : 0 < (Nat.choose (a+b) a : ℝ) := by exact_mod_cast Nat.choose_pos (show a ≤ a+b by omega)
  have hfac : (a.factorial : ℝ)*b.factorial*(Nat.choose (a+b) a : ℝ) = (a+b).factorial := by
    have he := Nat.choose_mul_factorial_mul_factorial (show a ≤ a+b by omega)
    rw [show a+b-a=b by omega] at he
    exact_mod_cast (by nlinarith [he] : a.factorial*b.factorial*(a+b).choose a = (a+b).factorial)
  have hroots : Real.sqrt (a.factorial)*Real.sqrt (b.factorial)*Real.sqrt (Nat.choose (a+b) a) =
      Real.sqrt ((a+b).factorial) := by
    rw [← Real.sqrt_mul (by positivity),← Real.sqrt_mul (by positivity),hfac]
  have he : rawPhi c a*rawPhi c b*Real.sqrt (Nat.choose (a+b) a) = rawPhi c (a+b) := by
    unfold rawPhi
    calc
      _ = c^(a+b)*(Real.sqrt (a.factorial)*Real.sqrt (b.factorial)*Real.sqrt (Nat.choose (a+b) a)) := by
        rw [pow_add]
        ring
      _ = _ := by rw [hroots]
  apply (div_eq_div_iff (rawPhi_pos c hc (a+b)).ne' (Real.sqrt_pos_of_pos hC).ne').mpr
  simpa only [one_mul] using he
lemma clippedPhi_binomial_split (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ,
      clippedPhi c (a+1)*clippedPhi c (b+1)/clippedPhi c (a+b) ≤
        C*Real.sqrt (((a+1 : ℕ) : ℝ)*(b+1))/Real.sqrt (Nat.choose (a+b) a) := by
  obtain ⟨C,hC,hcomp⟩ := clippedPhi_factorial_comparison c hc
  refine ⟨C^2*c^2,by positivity,?_⟩
  intro a b
  have hden := (hcomp (a+b)).1
  have hnum : clippedPhi c (a+1)*clippedPhi c (b+1) ≤
      (C*rawPhi c (a+1))*(C*rawPhi c (b+1)) := by
    exact mul_le_mul (by simpa only [rawPhi,mul_assoc] using (hcomp (a+1)).2)
      (by simpa only [rawPhi,mul_assoc] using (hcomp (b+1)).2)
      (clippedPhi_pos c (b+1)).le (mul_pos hC (rawPhi_pos c hc (a+1))).le
  calc
    _ ≤ clippedPhi c (a+1)*clippedPhi c (b+1)/rawPhi c (a+b) := by
      apply (div_le_div_iff₀ (clippedPhi_pos c (a+b)) (rawPhi_pos c hc (a+b))).mpr
      exact mul_le_mul_of_nonneg_left hden (mul_nonneg (clippedPhi_pos c (a+1)).le (clippedPhi_pos c (b+1)).le)
    _ ≤ (C*rawPhi c (a+1))*(C*rawPhi c (b+1))/rawPhi c (a+b) :=
      div_le_div_of_nonneg_right hnum (rawPhi_pos c hc (a+b)).le
    _ = C^2*c^2*(Real.sqrt (a+1)*Real.sqrt (b+1))*
        (rawPhi c a*rawPhi c b/rawPhi c (a+b)) := by
      rw [rawPhi_succ,rawPhi_succ]
      ring
    _ = _ := by
      rw [rawPhi_binomial_ratio c hc a b,← Real.sqrt_mul (by positivity)]
      push_cast
      ring
lemma clippedWeight_pos (c : ℝ) (d : List ℕ) : 0 < clippedWeight c d := by
  rw [clippedWeight_phi]
  exact mul_pos (by positivity) (clippedPhi_pos c _)
lemma clippedWeight_ratio_count_bound (c : ℝ) (parent d₁ d₂ : List ℕ) (a b : ℕ)
    (hz : zeros d₁+zeros d₂ ≤ zeros parent+2)
    (h₁ : inactive d₁ ≤ a+1) (h₂ : inactive d₂ ≤ b+1)
    (hp : a+b ≤ inactive parent) :
    clippedWeight c d₁*clippedWeight c d₂/clippedWeight c parent ≤
      16*clippedPhi c (a+1)*clippedPhi c (b+1)/clippedPhi c (a+b) := by
  have hnum : clippedWeight c d₁*clippedWeight c d₂ ≤
      (4 : ℝ)^(zeros parent+2)*clippedPhi c (a+1)*clippedPhi c (b+1) := by
    rw [clippedWeight_phi,clippedWeight_phi]
    have hzpow : (4 : ℝ)^(zeros d₁+zeros d₂) ≤ 4^(zeros parent+2) :=
      pow_le_pow_right₀ (by norm_num) hz
    have hphi : clippedPhi c (inactive d₁)*clippedPhi c (inactive d₂) ≤
        clippedPhi c (a+1)*clippedPhi c (b+1) :=
      mul_le_mul (clippedPhi_mono c h₁) (clippedPhi_mono c h₂)
        (clippedPhi_pos c _).le (clippedPhi_pos c _).le
    have he := mul_le_mul hzpow hphi (mul_nonneg (clippedPhi_pos c _).le (clippedPhi_pos c _).le)
      (show (0 : ℝ) ≤ 4^(zeros parent+2) by positivity)
    rw [pow_add] at he
    nlinarith only [he]
  have hden : (4 : ℝ)^(zeros parent)*clippedPhi c (a+b) ≤ clippedWeight c parent := by
    rw [clippedWeight_phi]
    exact mul_le_mul_of_nonneg_left (clippedPhi_mono c hp) (by positivity)
  have hDpos : (0 : ℝ) < 4^(zeros parent)*clippedPhi c (a+b) :=
    mul_pos (by positivity) (clippedPhi_pos c _)
  calc
    _ ≤ (clippedWeight c d₁*clippedWeight c d₂)/((4 : ℝ)^(zeros parent)*clippedPhi c (a+b)) := by
      apply (div_le_div_iff₀ (clippedWeight_pos c parent) hDpos).mpr
      exact mul_le_mul_of_nonneg_left hden (mul_nonneg (clippedWeight_pos c d₁).le (clippedWeight_pos c d₂).le)
    _ ≤ ((4 : ℝ)^(zeros parent+2)*clippedPhi c (a+1)*clippedPhi c (b+1))/
        ((4 : ℝ)^(zeros parent)*clippedPhi c (a+b)) :=
      div_le_div_of_nonneg_right hnum hDpos.le
    _ = _ := by
      rw [pow_add]
      norm_num
      field_simp
lemma inactive_append (d e : List ℕ) : inactive (d++e) = inactive d+inactive e := by
  simp [inactive,List.filter_append]
lemma zeros_append (d e : List ℕ) : zeros (d++e) = zeros d+zeros e := by
  simp [zeros,List.filter_append]
lemma inactive_perm {d e : List ℕ} (hp : d.Perm e) : inactive d = inactive e := by
  unfold inactive
  exact (hp.filter (fun k => k ≤ 1)).length_eq
lemma zeros_perm {d e : List ℕ} (hp : d.Perm e) : zeros d = zeros e := by
  unfold zeros
  exact (hp.filter (fun k => k = 0)).length_eq
lemma inactive_cons_bounds (p : ℕ) (d : List ℕ) :
    inactive d ≤ inactive (p :: d) ∧ inactive (p :: d) ≤ inactive d+1 := by
  unfold inactive
  by_cases hp : p ≤ 1 <;> simp [hp]
lemma zeros_cons_bounds (p : ℕ) (d : List ℕ) :
    zeros d ≤ zeros (p :: d) ∧ zeros (p :: d) ≤ zeros d+1 := by
  unfold zeros
  by_cases hp : p = 0 <;> simp [hp]
lemma clippedWeight_partition_binomial (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ pivot : ℕ, ∀ d e₁ e₂ : List ℕ, ∀ u v : ℕ,
      (e₁++e₂).Perm d →
      clippedWeight c (u :: e₁)*clippedWeight c (v :: e₂)/clippedWeight c (pivot :: d) ≤
        C*Real.sqrt (((inactive e₁+1 : ℕ) : ℝ)*(inactive e₂+1))/
          Real.sqrt (Nat.choose (inactive d) (inactive e₁)) := by
  obtain ⟨C,hC,hphi⟩ := clippedPhi_binomial_split c hc
  refine ⟨16*C,by positivity,?_⟩
  intro pivot d e₁ e₂ u v hp
  have hiz : inactive d = inactive e₁+inactive e₂ := by rw [← inactive_perm hp,inactive_append]
  have hzz : zeros d = zeros e₁+zeros e₂ := by rw [← zeros_perm hp,zeros_append]
  have hcounts := clippedWeight_ratio_count_bound c (pivot :: d) (u :: e₁) (v :: e₂)
    (inactive e₁) (inactive e₂)
    (by have h₁ := zeros_cons_bounds u e₁; have h₂ := zeros_cons_bounds v e₂
        have hp' := zeros_cons_bounds pivot d; omega)
    (inactive_cons_bounds u e₁).2 (inactive_cons_bounds v e₂).2
    (by rw [← hiz]; exact (inactive_cons_bounds pivot d).1)
  have he := mul_le_mul_of_nonneg_left (hphi (inactive e₁) (inactive e₂)) (by norm_num : (0 : ℝ) ≤ 16)
  rw [hiz]
  apply hcounts.trans
  convert he using 1 <;> ring
end WP
