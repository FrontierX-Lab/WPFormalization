import WPFormalization.HigherOrder.EndpointFormal

/-! Elementary Gevrey-one coefficient estimates for the actual finite formal operations. These are purely algebraic bounds; they assert no asymptotic matching with geometric quantities. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma factorial_product_cast_le (n k : ℕ) (hk : k ≤ n) :
    (k.factorial:ℝ)*((n-k).factorial:ℝ) ≤ n.factorial := by
  have he := Nat.le_of_dvd (Nat.factorial_pos (k+(n-k)))
    (Nat.factorial_mul_factorial_dvd_factorial_add k (n-k))
  rw [Nat.add_sub_of_le hk] at he
  exact_mod_cast he
lemma gevrey_one_pow_coeff (f : Series) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hf : ∀ n, |PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ)) (j n : ℕ) :
    |PowerSeries.coeff n (f^j)| ≤ C^j*B^n*(n.factorial:ℝ)*(Nat.choose (n+j) j:ℝ) := by
  induction j generalizing n with
  | zero =>
      by_cases hn : n=0
      · subst n;simp
      · have hb : (0:ℝ) ≤ B^n*(n.factorial:ℝ) := by positivity
        simpa [hn] using hb
  | succ j ih =>
      have ht (k : ℕ) (hk : k∈Finset.range (n+1)) :
          |PowerSeries.coeff k (f^j)*PowerSeries.coeff (n-k) f| ≤
            C^(j+1)*B^n*(n.factorial:ℝ)*(Nat.choose (k+j) j:ℝ) := by
        have hkn : k ≤ n := by have := Finset.mem_range.mp hk;omega
        rw [abs_mul]
        calc
          _ ≤ (C^j*B^k*(k.factorial:ℝ)*(Nat.choose (k+j) j:ℝ))*
              (C*B^(n-k)*((n-k).factorial:ℝ)) := mul_le_mul (ih k) (hf (n-k)) (abs_nonneg _) (by positivity)
          _ = (C^(j+1)*B^n*(Nat.choose (k+j) j:ℝ))*
              ((k.factorial:ℝ)*((n-k).factorial:ℝ)) := by
            have hp : B^k*B^(n-k)=B^n := by rw [←pow_add,Nat.add_sub_of_le hkn]
            rw [pow_succ,←hp]
            ring
          _ ≤ (C^(j+1)*B^n*(Nat.choose (k+j) j:ℝ))*(n.factorial:ℝ) :=
            mul_le_mul_of_nonneg_left (factorial_product_cast_le n k hkn) (by positivity)
          _ = _ := by ring
      rw [pow_succ,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      calc
        _ ≤ ∑ k∈Finset.range (n+1),|PowerSeries.coeff k (f^j)*PowerSeries.coeff (n-k) f| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k∈Finset.range (n+1),C^(j+1)*B^n*(n.factorial:ℝ)*(Nat.choose (k+j) j:ℝ) := Finset.sum_le_sum ht
        _ = (C^(j+1)*B^n*(n.factorial:ℝ))*
            (∑ k∈Finset.range (n+1),(Nat.choose (k+j) j:ℝ)) := by rw [Finset.mul_sum]
        _ = _ := by
          congr 1
          exact_mod_cast Nat.sum_range_add_choose n j
lemma finiteExp_gevrey_one (f : Series) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hf : ∀ n, |PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ)) (n : ℕ) :
    |PowerSeries.coeff n (finiteExp f)| ≤ Real.exp C*(8*B)^n*(n.factorial:ℝ) := by
  have ht (j : ℕ) (hj : j∈Finset.range (n+1)) :
      |PowerSeries.coeff n (f^j)/(j.factorial:ℝ)| ≤
        Real.exp C*(4*B)^n*(n.factorial:ℝ) := by
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj;omega
    have hchoose : (Nat.choose (n+j) j:ℝ) ≤ (4:ℝ)^n := by
      have hc : (Nat.choose (n+j) j:ℝ) ≤ (2:ℝ)^(n+j) := by exact_mod_cast Nat.choose_le_two_pow (n+j) j
      have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show n+j ≤ 2*n by omega)
      have hp' : (2:ℝ)^(2*n)=(4:ℝ)^n := by rw [pow_mul];norm_num
      exact hc.trans (hp.trans_eq hp')
    rw [abs_div,abs_of_pos (by exact_mod_cast Nat.factorial_pos j : (0:ℝ)<j.factorial)]
    calc
      _ ≤ (C^j*B^n*(n.factorial:ℝ)*(Nat.choose (n+j) j:ℝ))/(j.factorial:ℝ) :=
        div_le_div_of_nonneg_right (gevrey_one_pow_coeff f C B hC hB hf j n) (by positivity)
      _ ≤ (C^j*B^n*(n.factorial:ℝ)*(4:ℝ)^n)/(j.factorial:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hchoose (by positivity)) (by positivity)
      _ = (C^j/(j.factorial:ℝ))*((4*B)^n*(n.factorial:ℝ)) := by rw [mul_pow];ring
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp C hC j)
          (show 0 ≤ (4*B)^n*(n.factorial:ℝ) by positivity) using 1 <;> ring
  rw [finiteExp,PowerSeries.coeff_mk]
  calc
    _ ≤ ∑ j∈Finset.range (n+1),|PowerSeries.coeff n (f^j)/(j.factorial:ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j∈Finset.range (n+1),Real.exp C*(4*B)^n*(n.factorial:ℝ) := Finset.sum_le_sum ht
    _ = ((n:ℝ)+1)*(Real.exp C*(4*B)^n*(n.factorial:ℝ)) := by simp
    _ ≤ (2:ℝ)^n*(Real.exp C*(4*B)^n*(n.factorial:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.succ_le_of_lt (show n < (2:ℕ)^n from Nat.lt_two_pow_self)
    _ = _ := by
      have hp : (2:ℝ)^n*(4*B)^n=(8*B)^n := by rw [←mul_pow];congr 1;ring
      calc
        _ = Real.exp C*((2:ℝ)^n*(4*B)^n)*(n.factorial:ℝ) := by ring
        _ = _ := by rw [hp]
end WP.HigherOrder
namespace WP.HigherOrder
open PowerSeries
lemma gevrey_one_mul_coeff (f g : Series) (C D B : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hf : ∀ n, |PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ))
    (hg : ∀ n, |PowerSeries.coeff n g| ≤ D*B^n*(n.factorial:ℝ)) (n : ℕ) :
    |PowerSeries.coeff n (f*g)| ≤ (C*D)*(2*B)^n*(n.factorial:ℝ) := by
  have ht (k : ℕ) (hk : k∈Finset.range (n+1)) :
      |PowerSeries.coeff k f*PowerSeries.coeff (n-k) g| ≤ (C*D)*B^n*(n.factorial:ℝ) := by
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk;omega
    rw [abs_mul]
    calc
      _ ≤ (C*B^k*(k.factorial:ℝ))*(D*B^(n-k)*((n-k).factorial:ℝ)) :=
        mul_le_mul (hf k) (hg (n-k)) (abs_nonneg _) (by positivity)
      _ = ((C*D)*B^n)*((k.factorial:ℝ)*((n-k).factorial:ℝ)) := by
        have hp : B^k*B^(n-k)=B^n := by rw [←pow_add,Nat.add_sub_of_le hkn]
        rw [←hp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_product_cast_le n k hkn) (by positivity)
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ ≤ ∑ k∈Finset.range (n+1),|PowerSeries.coeff k f*PowerSeries.coeff (n-k) g| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k∈Finset.range (n+1),(C*D)*B^n*(n.factorial:ℝ) := Finset.sum_le_sum ht
    _ = ((n:ℝ)+1)*((C*D)*B^n*(n.factorial:ℝ)) := by simp
    _ ≤ (2:ℝ)^n*((C*D)*B^n*(n.factorial:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.succ_le_of_lt (show n < (2:ℕ)^n from Nat.lt_two_pow_self)
    _ = _ := by rw [mul_pow];ring
lemma gevrey_one_mul_combine (f g : Series) (C D B E : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hf : ∀ n, |PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ))
    (hg : ∀ n, |PowerSeries.coeff n g| ≤ D*E^n*(n.factorial:ℝ)) (n : ℕ) :
    |PowerSeries.coeff n (f*g)| ≤ (C*D)*(2*(B+E))^n*(n.factorial:ℝ) := by
  apply gevrey_one_mul_coeff f g C D (B+E) hC hD (by positivity)
  · intro k
    apply (hf k).trans
    gcongr
    linarith
  · intro k
    apply (hg k).trans
    gcongr
    linarith
lemma finiteLog_gevrey_one (f : Series) (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hf : ∀ n, |PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ)) (n : ℕ) :
    |PowerSeries.coeff n (finiteLog f)| ≤ (8*(C+1)*(B+1))^n*(n.factorial:ℝ) := by
  have hfsub (k : ℕ) : |PowerSeries.coeff k (f-1)| ≤ (C+1)*(B+1)^k*(k.factorial:ℝ) := by
    rw [map_sub]
    by_cases hk0 : k=0
    · subst k
      simp only [PowerSeries.coeff_one,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,ite_true]
      have hb : |constantCoeff f| ≤ C := by simpa using hf 0
      calc
        _ ≤ |constantCoeff f|+1 := by simpa only [abs_one, PowerSeries.coeff_zero_eq_constantCoeff] using abs_sub (constantCoeff f) (1:ℝ)
        _ ≤ _ := add_le_add hb le_rfl
    · simp only [PowerSeries.coeff_one,if_neg hk0,sub_zero]
      apply (hf k).trans
      gcongr <;> linarith
  have ht (j : ℕ) (hj : j∈Finset.Icc 1 n) :
      |(-1:ℝ)^(j+1)*PowerSeries.coeff n ((f-1)^j)/(j:ℝ)| ≤
        (4*(C+1)*(B+1))^n*(n.factorial:ℝ) := by
    have hj' := Finset.mem_Icc.mp hj
    have hjR : (1:ℝ) ≤ j := by exact_mod_cast hj'.1
    have hjpos : (0:ℝ)<j := by linarith
    have hchoose : (Nat.choose (n+j) j:ℝ) ≤ (4:ℝ)^n := by
      have hc : (Nat.choose (n+j) j:ℝ) ≤ (2:ℝ)^(n+j) := by exact_mod_cast Nat.choose_le_two_pow (n+j) j
      have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show n+j ≤ 2*n by omega)
      have hp' : (2:ℝ)^(2*n)=(4:ℝ)^n := by rw [pow_mul];norm_num
      exact hc.trans (hp.trans_eq hp')
    rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_pos hjpos]
    calc
      _ ≤ |PowerSeries.coeff n ((f-1)^j)| := div_le_self (abs_nonneg _) hjR
      _ ≤ (C+1)^j*(B+1)^n*(n.factorial:ℝ)*(Nat.choose (n+j) j:ℝ) :=
        gevrey_one_pow_coeff (f-1) (C+1) (B+1) (by positivity) (by positivity) hfsub j n
      _ ≤ (C+1)^n*(B+1)^n*(n.factorial:ℝ)*(4:ℝ)^n := by
        apply mul_le_mul _ hchoose (Nat.cast_nonneg _) (by positivity)
        have hp := pow_le_pow_right₀ (by linarith : (1:ℝ)≤C+1) hj'.2
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
      _ = _ := by simp only [mul_pow];ring
  rw [finiteLog,PowerSeries.coeff_mk]
  calc
    _ ≤ ∑ j∈Finset.Icc 1 n,|(-1:ℝ)^(j+1)*PowerSeries.coeff n ((f-1)^j)/(j:ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j∈Finset.Icc 1 n,(4*(C+1)*(B+1))^n*(n.factorial:ℝ) := Finset.sum_le_sum ht
    _ = (n:ℝ)*((4*(C+1)*(B+1))^n*(n.factorial:ℝ)) := by simp
    _ ≤ (2:ℝ)^n*((4*(C+1)*(B+1))^n*(n.factorial:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show n ≤ (2:ℕ)^n from Nat.le_of_lt Nat.lt_two_pow_self)
    _ = _ := by
      have hp : (2:ℝ)^n*(4*(C+1)*(B+1))^n=(8*(C+1)*(B+1))^n := by rw [←mul_pow];congr 1;ring
      calc
        _ = ((2:ℝ)^n*(4*(C+1)*(B+1))^n)*(n.factorial:ℝ) := by ring
        _ = _ := by rw [hp]
end WP.HigherOrder
