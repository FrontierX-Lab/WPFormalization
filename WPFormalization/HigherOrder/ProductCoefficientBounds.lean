import WPFormalization.HigherOrder.FiniteRemainderAlgebra
/-! Two known coefficient families with uniform geometric bounds have
a uniform geometric product coefficient bound on the same degree scale. -/
noncomputable section
namespace WP.HigherOrder
lemma product_coeff_scaled_exponential (f g:PowerSeries ℝ) (n:ℕ) (C B T:ℝ)
    (hC:0 ≤ C) (hB:0 ≤ B) (hT:0 ≤ T)
    (hf:∀i:ℕ,i ≤ n→|PowerSeries.coeff i f| ≤ C*B^i*T^(2*i))
    (hg:∀i:ℕ,i ≤ n→|PowerSeries.coeff i g| ≤ C*B^i*T^(2*i)) :
    |PowerSeries.coeff n (f*g)| ≤ (2*C^2)*(2*max B 1)^n*T^(2*n):=by
  have hterm (i:ℕ) (hi:i∈Finset.range (n+1)) :
      |PowerSeries.coeff i f*PowerSeries.coeff (n-i) g| ≤ C^2*B^n*T^(2*n):=by
    have hiN:i ≤ n:=by have hh:=Finset.mem_range.mp hi;omega
    rw[abs_mul]
    apply (mul_le_mul (hf i hiN) (hg (n-i) (by omega)) (abs_nonneg _) (by positivity)).trans_eq
    have hBpow:B^i*B^(n-i)=B^n:=by rw[←pow_add,Nat.add_sub_of_le hiN]
    have hTpow:T^(2*i)*T^(2*(n-i))=T^(2*n):=by rw[←pow_add];congr 1;omega
    calc
      _=C^2*(B^i*B^(n-i))*(T^(2*i)*T^(2*(n-i))):=by ring
      _=_:=by rw[hBpow,hTpow]
  have hcoeff:|PowerSeries.coeff n (f*g)| ≤ (n+1:ℕ)* (C^2*B^n*T^(2*n)):=by
    rw[PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans_eq (by
      simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]))
  let R:=max B 1
  have hR:0 ≤ R:=hB.trans (le_max_left _ _)
  have hnp:(n+1:ℕ) ≤ (2:ℝ)^(n+1):=by exact_mod_cast (Nat.le_of_lt (n+1).lt_two_pow_self)
  have hBp:B^n ≤ R^n:=pow_le_pow_left₀ hB (le_max_left _ _) n
  have hb:(n+1:ℕ)*B^n ≤ 2*(2*R)^n:=by
    have hp:=mul_le_mul hnp hBp (pow_nonneg hB _) (by positivity:(0:ℝ) ≤ (2:ℝ)^(n+1))
    exact hp.trans_eq (by rw[pow_succ,mul_pow];ring)
  apply hcoeff.trans
  have hbmul:=mul_le_mul_of_nonneg_right hb (mul_nonneg (sq_nonneg C) (pow_nonneg hT (2*n)))
  dsimp[R] at hbmul
  convert hbmul using 1 <;>ring
end WP.HigherOrder
