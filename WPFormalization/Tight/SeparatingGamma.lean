import WPFormalization.Critical.CutGammaConvolution

/-! The full ordered positive-complexity Gamma convolution for original F.3.
The square-root denominator is preserved using H ≤ Q ∏h_i; the existing
factorial allocation estimate then supplies the exact inverse power H^(-(Q-1)).
All Gamma arguments are positive integers; no deferred Gamma identity is used. -/

noncomputable section
namespace WP.TightSeparating
open Set Finset
open scoped BigOperators

/-- The exact integer-complexity weight in (F.7). -/
def gammaWeight (h : ℕ) : ℝ := Real.Gamma (h : ℝ) / Real.sqrt (h : ℝ)

/-- Every ordered positive-complexity allocation h_i=j_i+1, with sum N+Q. -/
def gammaAllocation (Q N : ℕ) : ℝ :=
  ∑ l ∈ finsuppAntidiag (range Q) N,
    ∏ i ∈ range Q, gammaWeight (l i+1)

lemma gammaWeight_pos (h : ℕ) (hh : 1 ≤ h) : 0 < gammaWeight h := by
  have hr : 0 < (h : ℝ) := by exact_mod_cast (show 0 < h by omega)
  exact div_pos (Real.Gamma_pos_of_pos hr) (Real.sqrt_pos.mpr hr)

lemma sqrt_sum_le_card_mul_prod (Q : ℕ) (w : ℕ → ℝ)
    (hw : ∀ i ∈ range Q, 1 ≤ w i) :
    Real.sqrt (∑ i ∈ range Q, w i) ≤
      Real.sqrt (Q : ℝ) * ∏ i ∈ range Q, Real.sqrt (w i) := by
  have hsum : (∑ i ∈ range Q, w i) ≤ (Q : ℝ) * ∏ i ∈ range Q, w i := by
    calc
      _ ≤ ∑ _i ∈ range Q, ∏ j ∈ range Q, w j :=
        sum_le_sum (fun i hi => by
          have hh := prod_le_prod_of_subset_of_one_le₀
            (singleton_subset_iff.mpr hi) (fun j hj => by
              have he : j=i := mem_singleton.mp hj
              subst j
              exact zero_le_one.trans (hw i hi))
            (fun j hj _ => hw j hj)
          simpa using hh)
      _ = _ := by simp
  calc
    _ ≤ Real.sqrt ((Q : ℝ) * ∏ i ∈ range Q, w i) := Real.sqrt_le_sqrt hsum
    _ = _ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg Q), Real.sqrt_prod _ (fun i hi => (zero_le_one.trans (hw i hi)))]

lemma gamma_allocation_sqrt_bound (Q N : ℕ) :
    Real.sqrt (N+Q : ℕ) * gammaAllocation Q N ≤
      Real.sqrt (Q : ℝ) * (3 : ℝ)^Q * (N.factorial : ℝ) := by
  have hterm (l : ℕ →₀ ℕ) (hl : l ∈ finsuppAntidiag (range Q) N) :
      Real.sqrt (N+Q : ℕ) * (∏ i ∈ range Q, gammaWeight (l i+1)) ≤
        Real.sqrt (Q : ℝ) * ∏ i ∈ range Q, ((l i).factorial : ℝ) := by
    have hsum := (mem_finsuppAntidiag.mp hl).1
    have hsumR : (∑ i ∈ range Q, ((l i:ℝ)+1)) = (N+Q : ℕ) := by
      simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one]
      exact_mod_cast congrArg (fun a : ℕ => a+Q) hsum
    have hroot := sqrt_sum_le_card_mul_prod Q (fun i => (l i:ℝ)+1)
      (fun i _ => by have hi := Nat.cast_nonneg (α := ℝ) (l i); linarith)
    rw [hsumR] at hroot
    have hprodpos : 0 < ∏ i ∈ range Q, Real.sqrt ((l i:ℝ)+1) :=
      prod_pos (fun i _ => Real.sqrt_pos.mpr (by positivity))
    have hfactor : (∏ i ∈ range Q, gammaWeight (l i+1)) =
        (∏ i ∈ range Q, ((l i).factorial : ℝ)) /
          (∏ i ∈ range Q, Real.sqrt ((l i:ℝ)+1)) := by
      simp only [gammaWeight,Nat.cast_add,Nat.cast_one,Real.Gamma_nat_eq_factorial,prod_div_distrib]
    rw [hfactor,←mul_div_assoc]
    apply (div_le_iff₀ hprodpos).mpr
    have he := mul_le_mul_of_nonneg_right hroot
      (show 0 ≤ ∏ i ∈ range Q, ((l i).factorial : ℝ) by positivity)
    nlinarith only [he]
  calc
    _ = ∑ l ∈ finsuppAntidiag (range Q) N,
        Real.sqrt (N+Q : ℕ) * ∏ i ∈ range Q, gammaWeight (l i+1) := by
      rw [gammaAllocation,mul_sum]
    _ ≤ ∑ l ∈ finsuppAntidiag (range Q) N,
        Real.sqrt (Q : ℝ) * ∏ i ∈ range Q, ((l i).factorial : ℝ) := sum_le_sum hterm
    _ = Real.sqrt (Q : ℝ) * (∑ l ∈ finsuppAntidiag (range Q) N,
        ∏ i ∈ range Q, ((l i).factorial : ℝ)) := by rw [mul_sum]
    _ ≤ Real.sqrt (Q : ℝ) * ((3 : ℝ)^Q * (N.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (Critical.cutStable_factorial_allocation_bound Q N)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

lemma gamma_allocation_ratio_bound (Q N : ℕ) (hQ : 1 ≤ Q) :
    gammaAllocation Q N / gammaWeight (N+Q) ≤
      (Real.sqrt (Q : ℝ) * (3 : ℝ)^Q) *
        ((N.factorial : ℝ) / ((N+Q-1).factorial : ℝ)) := by
  have hH : 0 < (N+Q : ℕ) := by omega
  have hHR : 0 < (N+Q : ℕ) := hH
  have hGamma : Real.Gamma ((N+Q : ℕ) : ℝ) = ((N+Q-1).factorial : ℝ) := by
    have he : N+Q=(N+Q-1)+1 := by omega
    conv_lhs => rw [he,Nat.cast_add,Nat.cast_one,Real.Gamma_nat_eq_factorial]
  have hsqrt : 0 < Real.sqrt ((N+Q : ℕ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hH)
  have hfac : 0 < ((N+Q-1).factorial : ℝ) := by positivity
  rw [gammaWeight,hGamma,div_div_eq_mul_div]
  apply (div_le_iff₀ hfac).mpr
  have hh := gamma_allocation_sqrt_bound Q N
  convert hh using 1 <;> field_simp <;> ring

lemma factorial_ratio_le_inverse_power (N d : ℕ) :
    (N.factorial : ℝ) / ((N+d).factorial : ℝ) ≤ 1 / ((N+1 : ℕ) : ℝ)^d := by
  have he := Nat.factorial_mul_ascFactorial N d
  have hpow := Nat.pow_succ_le_ascFactorial (N+1) d
  have hprod : ((N+1 : ℕ) : ℝ)^d ≤ ((N+1).ascFactorial d : ℝ) := by exact_mod_cast hpow
  have heR : (N.factorial : ℝ) * ((N+1).ascFactorial d : ℝ) = ((N+d).factorial : ℝ) := by exact_mod_cast he
  have hfac : 0 < (N.factorial : ℝ) := by positivity
  have htot : 0 < ((N+d).factorial : ℝ) := by positivity
  have hnp : 0 < ((N+1 : ℕ) : ℝ)^d := by positivity
  apply (div_le_div_iff₀ htot hnp).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod hfac.le]

lemma gamma_allocation_genus_rate (Q H : ℕ) (hQ : 2 ≤ Q) (hH : 2*Q ≤ H) :
    gammaAllocation Q (H-Q) / gammaWeight H ≤
      (Real.sqrt (Q : ℝ) * (3 : ℝ)^Q * (2 : ℝ)^(Q-1)) / (H : ℝ)^(Q-1) := by
  have hQH : Q ≤ H := by omega
  have hHp : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hHR : (2 : ℝ) * Q ≤ H := by exact_mod_cast hH
  have hsub : ((H-Q+1 : ℕ) : ℝ) = (H : ℝ) - Q + 1 := by
    rw [Nat.cast_add,Nat.cast_sub hQH,Nat.cast_one]
  have hbase : (H : ℝ)/2 ≤ ((H-Q+1 : ℕ) : ℝ) := by rw [hsub];linarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ (H : ℝ)/2 by positivity) hbase (Q-1)
  have hratio := factorial_ratio_le_inverse_power (H-Q) (Q-1)
  have he : H-Q+(Q-1)=H-1 := by omega
  rw [he] at hratio
  have hinv : 1 / ((H-Q+1 : ℕ) : ℝ)^(Q-1) ≤
      (2 : ℝ)^(Q-1) / (H : ℝ)^(Q-1) := by
    have hb : 0 < ((H : ℝ)/2)^(Q-1) := by positivity
    have hv := one_div_le_one_div_of_le hb hpow
    simpa only [div_pow,one_div_div] using hv
  have hs := gamma_allocation_ratio_bound Q (H-Q) (by omega)
  rw [Nat.sub_add_cancel hQH] at hs
  have Cpos : 0 ≤ Real.sqrt (Q : ℝ) * (3 : ℝ)^Q := by positivity
  calc
    _ ≤ _ := hs
    _ ≤ (Real.sqrt (Q : ℝ) * (3 : ℝ)^Q) *
        ((2 : ℝ)^(Q-1)/(H : ℝ)^(Q-1)) :=
      mul_le_mul_of_nonneg_left (hratio.trans hinv) Cpos
    _ = _ := by ring

end WP.TightSeparating
