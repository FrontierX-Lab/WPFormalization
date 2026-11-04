import WPFormalization.Weighted.LabelSum
import WPFormalization.Weighted.BinomialEnvelope

/-! Finite binomial generating estimates and label entropy decay, including genus zero. -/
noncomputable section
namespace WP
lemma binomialWeight_le_total (N j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (N.choose j : ℝ)*x^j ≤ (1+x)^N := by
  by_cases hj : j ≤ N
  · rw [← binomialWeight_sum]
    change binomialWeight N x j ≤ _
    apply Finset.single_le_sum
    · intro i hi
      exact binomialWeight_nonneg N x hx i
    · exact Finset.mem_range.mpr (by omega)
  · simp [Nat.choose_eq_zero_of_lt (show N < j by omega),show 0 ≤ (1+x)^N by positivity]
lemma binomialPartial_generating (R s : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ j ∈ Finset.range (s+1), (R.choose j : ℝ))*x^s ≤ (1+x)^R := by
  calc
    _ = ∑ j ∈ Finset.range (s+1), (R.choose j : ℝ)*x^s := by rw [Finset.sum_mul]
    _ ≤ ∑ j ∈ Finset.range (s+1), binomialWeight R x j := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact pow_le_pow_of_le_one hx hx1 (by have := Finset.mem_range.mp hj; omega)
    _ ≤ ∑ j ∈ Finset.range (R+1), binomialWeight R x j := by
      by_cases hs : s ≤ R
      · exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) (fun j hj hj' => binomialWeight_nonneg R x hx j)
      · have hsub : Finset.range (R+1) ⊆ Finset.range (s+1) := Finset.range_mono (by omega)
        have he := Finset.sum_subset (f := binomialWeight R x) hsub (by
          intro j hj hj'
          have hjR : R < j := by
            have hh : ¬ j < R+1 := by simpa only [Finset.mem_range] using hj'
            omega
          simp [binomialWeight,Nat.choose_eq_zero_of_lt hjR])
        exact he.symm.le
    _ = _ := binomialWeight_sum R x
lemma weightedLabelSum_generating (I R s : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (weightedLabelSum I R s)^2*x^(2*s) ≤ (1+x)^(I+2*R) := by
  have he := weightedLabelSum_bound I R s
  have hA : 0 ≤ weightedLabelSum I R s := by
    unfold weightedLabelSum
    positivity
  have hB : 0 ≤ Real.sqrt ((I+R).choose s)*Real.sqrt (∑ j ∈ Finset.range (s+1), (R.choose j : ℝ)) := by positivity
  have hsq := pow_le_pow_left₀ hA he 2
  rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)] at hsq
  have hsq' := mul_le_mul_of_nonneg_right hsq (show 0 ≤ x^(2*s) by positivity)
  have hchoose := binomialWeight_le_total (I+R) s x hx
  have hpartial := binomialPartial_generating R s x hx hx1
  calc
    _ ≤ (((I+R).choose s : ℝ)*x^s)*((∑ j ∈ Finset.range (s+1), (R.choose j : ℝ))*x^s) := by
      convert hsq' using 1 <;> ring
    _ ≤ (1+x)^(I+R)*(1+x)^R :=
      mul_le_mul hchoose hpartial (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega
lemma label_generating_sixth (A D x : ℝ) (I R s N k : ℕ)
    (_hA : 0 ≤ A) (_hD : 0 ≤ D) (hx : 0 < x) (hx1 : x ≤ 1) (hs : s ≤ k)
    (hexp : 3*(I+2*R)+N ≤ 6*N)
    (hgen : A^2*x^(2*s) ≤ (1+x)^(I+2*R))
    (hmean : (1+x)^N ≤ D*x^k) : A^6*(1+x)^N ≤ D^6 := by
  have hB : 1 ≤ 1+x := by linarith
  have h3 := pow_le_pow_left₀ (show 0 ≤ A^2*x^(2*s) by positivity) hgen 3
  simp only [mul_pow,← pow_mul] at h3
  have h3' : A^6*x^(6*s) ≤ (1+x)^(3*(I+2*R)) := by
    simpa only [show 2*3=6 by omega,show (2*s)*3=6*s by omega,
      show (I+2*R)*3=3*(I+2*R) by omega] using h3
  have h6 := pow_le_pow_left₀ (show 0 ≤ (1+x)^N by positivity) hmean 6
  simp only [mul_pow,← pow_mul] at h6
  have h6' : (1+x)^(6*N) ≤ D^6*x^(6*k) := by
    simpa only [show N*6=6*N by omega,show k*6=6*k by omega] using h6
  have hxpow : x^(6*k) ≤ x^(6*s) := pow_le_pow_of_le_one hx.le hx1 (by omega)
  have hall : x^(6*s)*(A^6*(1+x)^N) ≤ x^(6*s)*D^6 := by
    calc
      _ = (A^6*x^(6*s))*(1+x)^N := by ring
      _ ≤ (1+x)^(3*(I+2*R))*(1+x)^N := mul_le_mul_of_nonneg_right h3' (by positivity)
      _ = (1+x)^(3*(I+2*R)+N) := by rw [pow_add]
      _ ≤ (1+x)^(6*N) := pow_le_pow_right₀ hB hexp
      _ ≤ D^6*x^(6*k) := h6'
      _ ≤ D^6*x^(6*s) := mul_le_mul_of_nonneg_left hxpow (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (pow_pos hx _)).mp hall
lemma binomial_mean_log (N k : ℕ) (hk : 1 ≤ k) (hN : 2*k ≤ N) :
    (k : ℝ) ≤ N*Real.log (1+(k : ℝ)/(N-k : ℕ)) := by
  have hNk : (0 : ℝ) < (N-k : ℕ) := by exact_mod_cast (show 0 < N-k by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he := Real.one_sub_inv_le_log_of_pos
    (show 0 < 1+(k : ℝ)/(N-k : ℕ) by positivity)
  have hid : (N : ℝ)*(1-(1+(k : ℝ)/(N-k : ℕ))⁻¹) = k := by
    have hbase : 1+(k : ℝ)/(N-k : ℕ) = (N : ℝ)/(N-k : ℕ) := by
      field_simp [hNk.ne']
      rw [Nat.cast_sub (by omega)]
      ring
    rw [hbase,inv_div]
    field_simp [hNR.ne']
    rw [Nat.cast_sub (by omega)]
    ring
  calc
    _ = (N : ℝ)*(1-(1+(k : ℝ)/(N-k : ℕ))⁻¹) := hid.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left he hNR.le
lemma weightedLabelSum_entropy (I R N k s : ℕ) (hk : 1 ≤ k) (hN : 2*k ≤ N)
    (hIR : I+R ≤ N) (hR : 3*R ≤ 2*N) (hs : s ≤ k) :
    weightedLabelSum I R s ≤ 4*((k : ℝ)+1)*(N.choose k : ℝ)*Real.exp (-(k : ℝ)/6) := by
  let x : ℝ := (k : ℝ)/(N-k : ℕ)
  let D : ℝ := 4*((k : ℝ)+1)*(N.choose k : ℝ)
  have hx : 0 < x := by dsimp only [x]; exact div_pos (by exact_mod_cast (show 0<k by omega)) (by exact_mod_cast (show 0<N-k by omega))
  have hx1 : x ≤ 1 := by
    dsimp only [x]
    apply (div_le_one (by exact_mod_cast (show 0<N-k by omega))).mpr
    exact_mod_cast (show k ≤ N-k by omega)
  have hA : 0 ≤ weightedLabelSum I R s := by unfold weightedLabelSum; positivity
  have hD : 0 < D := by
    dsimp only [D]
    have hch : 0 < N.choose k := Nat.choose_pos (by omega)
    positivity
  have he := label_generating_sixth (weightedLabelSum I R s) D x I R s N k hA hD.le hx hx1 hs
    (by omega) (weightedLabelSum_generating I R s x hx.le hx1)
    (binomialWeight_mean_lower N k hk hN)
  have hlog := binomial_mean_log N k hk hN
  have hexp : Real.exp (k : ℝ) ≤ (1+x)^N := by
    rw [← Real.exp_log (show 0 < (1+x)^N by positivity),Real.log_pow]
    exact Real.exp_le_exp.mpr hlog
  have hh : (weightedLabelSum I R s)^6*Real.exp (k : ℝ) ≤ D^6 :=
    (mul_le_mul_of_nonneg_left hexp (by positivity)).trans he
  have hc : (weightedLabelSum I R s)^6 ≤ (D*Real.exp (-(k : ℝ)/6))^6 := by
    apply (mul_le_mul_iff_left₀ (Real.exp_pos (k : ℝ))).mp
    calc
      _ ≤ D^6 := hh
      _ = _ := by
        have hExp : (Real.exp (-(k : ℝ)/6))^6*Real.exp (k : ℝ) = 1 := by
          rw [← Real.exp_nat_mul,← Real.exp_add]
          convert Real.exp_zero using 1 <;> ring
        calc
          D^6 = D^6*1 := by ring
          _ = D^6*((Real.exp (-(k : ℝ)/6))^6*Real.exp (k : ℝ)) := by rw [hExp]
          _ = _ := by ring
  exact le_of_pow_le_pow_left₀ (by norm_num : (6:ℕ) ≠ 0) (by positivity) hc
lemma choose_delete_two (I u : ℕ) (hu : 2 ≤ u) :
    I.choose u ≤ I^2*(I-2).choose (u-2) := by
  have he := Nat.choose_mul (n := I) (k := u) (s := 2) hu
  have hupos : 1 ≤ u.choose 2 := Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos hu).ne'
  calc
    _ ≤ I.choose u * u.choose 2 := by nlinarith
    _ = I.choose 2*(I-2).choose (u-2) := he
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.choose_le_pow I 2)
lemma sqrt_choose_delete_two (I u : ℕ) (hu : 2 ≤ u) :
    Real.sqrt (I.choose u) ≤ (I : ℝ)*Real.sqrt ((I-2).choose (u-2)) := by
  have he : (I.choose u : ℝ) ≤ (I : ℝ)^2*((I-2).choose (u-2) : ℝ) := by
    exact_mod_cast choose_delete_two I u hu
  have hr := Real.sqrt_le_sqrt he
  rw [Real.sqrt_mul (sq_nonneg (I : ℝ)),Real.sqrt_sq (Nat.cast_nonneg I)] at hr
  exact hr
lemma sum_antidiagonal_shift_two (f : ℕ × ℕ → ℝ) (k : ℕ) :
    (∑ uv ∈ Finset.HasAntidiagonal.antidiagonal (k+2), if 2 ≤ uv.1 then f (uv.1-2,uv.2) else 0) =
      ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal k, f uv := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun uv huv => (uv.1-2,uv.2))
  · intro uv huv
    have hm := (Finset.mem_filter.mp huv).1
    have hu := (Finset.mem_filter.mp huv).2
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hm ⊢
    omega
  · intro uv huv uv' huv' he
    have hu := (Finset.mem_filter.mp huv).2
    have hu' := (Finset.mem_filter.mp huv').2
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    apply Prod.ext <;> dsimp only at he1 he2 ⊢ <;> omega
  · intro uv huv
    refine ⟨(uv.1+2,uv.2),?_,?_⟩
    · simp only [Finset.mem_filter,Finset.HasAntidiagonal.mem_antidiagonal]
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
      exact ⟨by omega,by omega⟩
    · simp
  · intro uv huv
    rfl
lemma weightedLabelSum_genus_zero (I R k : ℕ) :
    (∑ uv ∈ Finset.HasAntidiagonal.antidiagonal (k+2), if 2 ≤ uv.1 then
      Real.sqrt (I.choose uv.1)*(R.choose uv.2 : ℝ) else 0) ≤
      (I : ℝ)*weightedLabelSum (I-2) R k := by
  calc
    _ ≤ ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal (k+2), if 2 ≤ uv.1 then
        (I : ℝ)*Real.sqrt ((I-2).choose (uv.1-2))*(R.choose uv.2 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro uv huv
      by_cases hu : 2 ≤ uv.1
      · simp only [hu,ite_true]
        exact mul_le_mul_of_nonneg_right (sqrt_choose_delete_two I uv.1 hu) (Nat.cast_nonneg _)
      · simp only [hu,ite_false,le_refl]
    _ = _ := by
      rw [sum_antidiagonal_shift_two
        (fun uv => (I : ℝ)*Real.sqrt ((I-2).choose uv.1)*(R.choose uv.2 : ℝ)) k]
      unfold weightedLabelSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro uv huv
      ring
lemma weightedLabelSum_entropy_all (I R N k s : ℕ) (hN : 2*k ≤ N)
    (hIR : I+R ≤ N) (hR : 3*R ≤ 2*N) (hs : s ≤ k) :
    weightedLabelSum I R s ≤ 4*((k : ℝ)+1)*(N.choose k : ℝ)*Real.exp (-(k : ℝ)/6) := by
  by_cases hk : k=0
  · have hs0 : s=0 := by omega
    subst k
    subst s
    norm_num [weightedLabelSum]
  · exact weightedLabelSum_entropy I R N k s (by omega) hN hIR hR hs
lemma weightedLabelSum_genus_zero_entropy (I R N k : ℕ) (hN : 2*k ≤ N)
    (hIR : I+R ≤ N) (hR : 3*R ≤ 2*N) :
    (∑ uv ∈ Finset.HasAntidiagonal.antidiagonal (k+2), if 2 ≤ uv.1 then
      Real.sqrt (I.choose uv.1)*(R.choose uv.2 : ℝ) else 0) ≤
      (I : ℝ)*(4*((k : ℝ)+1)*(N.choose k : ℝ)*Real.exp (-(k : ℝ)/6)) := by
  exact (weightedLabelSum_genus_zero I R k).trans
    (mul_le_mul_of_nonneg_left
      (weightedLabelSum_entropy_all (I-2) R N k k hN (by omega) hR le_rfl) (Nat.cast_nonneg I))
end WP
