import WPFormalization.Analysis.PoissonStirlingLog
import WPFormalization.Analysis.RealKernelRoot
/-! Endpoint-uniform logarithmic comparison of the actual one-boundary model: LogModelStirling. -/
noncomputable section
namespace WP.Coefficients
open WP.Analysis WP.HigherOrder
lemma factorial_log_normalizer_identity (n:ℕ)(hn:1≤n):
    Real.log (n.factorial:ℝ)-((n:ℝ)*Real.log n-n)=
      Real.log n/2+Real.log (2*Real.pi)/2-poissonLogNormalizer n:=by
  have hnR:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hg:0<Real.Gamma (n:ℝ):=Real.Gamma_pos_of_pos hnR
  have hfac:(n.factorial:ℝ)=(n:ℝ)*Real.Gamma n:=by
    rw[←Real.Gamma_nat_eq_factorial,Real.Gamma_add_one hnR.ne']
  rw[hfac,Real.log_mul hnR.ne' hg.ne']
  dsimp[poissonLogNormalizer]
  ring
lemma factorial_log_uniform_bound:
    ∃C:ℝ,0<C∧∀n:ℕ,|Real.log (n.factorial:ℝ)-((n:ℝ)*Real.log n-n)|≤C*Real.log ((n:ℝ)+1):=by
  let b:ℝ:=|Real.log (2*Real.pi)|/2+8
  have hb:0<b:=by dsimp[b];positivity
  let C:ℝ:=1/2+b/Real.log 2
  have hlog2:0<Real.log 2:=Real.log_pos (by norm_num)
  have hC:0<C:=by dsimp[C];positivity
  refine ⟨C,hC,?_⟩
  intro n
  by_cases hn:n=0
  · subst n
    simp
  · have hn1:1≤n:=by omega
    have hnR:(1:ℝ)≤n:=by exact_mod_cast hn1
    have hnpos:0<(n:ℝ):=zero_lt_one.trans_le hnR
    have hN:=poissonLogNormalizer_uniform_error 0 n hnR
    simp only[inversePowerTruncation,Finset.sum_range_one,PowerSeries.coeff_zero_eq_constantCoeff,
      poissonStirlingLog_constant,zero_div,sub_zero,Nat.zero_add,pow_one,Nat.factorial_one,Nat.cast_one,mul_one] at hN
    have hN8:|poissonLogNormalizer n|≤8:=hN.trans (by norm_num;exact div_le_self (by norm_num) hnR)
    have hlogn:0≤Real.log (n:ℝ):=Real.log_nonneg hnR
    have hlogle:Real.log (n:ℝ)≤Real.log ((n:ℝ)+1):=Real.log_le_log hnpos (by linarith)
    have hloglow:Real.log 2≤Real.log ((n:ℝ)+1):=Real.log_le_log (by norm_num) (by linarith)
    have hbase:b≤b/Real.log 2*Real.log ((n:ℝ)+1):=by
      have he:=mul_le_mul_of_nonneg_left hloglow (div_nonneg hb.le hlog2.le)
      have hc:b/Real.log 2*Real.log 2=b:=by field_simp
      rwa[hc] at he
    rw[factorial_log_normalizer_identity n hn1]
    have ht:=abs_sub_le (Real.log (n:ℝ)/2+Real.log (2*Real.pi)/2) 0 (poissonLogNormalizer n)
    simp only[sub_zero,zero_sub,abs_neg] at ht
    have hu:=abs_add_le (Real.log (n:ℝ)/2) (Real.log (2*Real.pi)/2)
    have hl1:|Real.log (n:ℝ)/2|=Real.log (n:ℝ)/2:=abs_of_nonneg (by positivity)
    have hl2:|Real.log (2*Real.pi)/2|=|Real.log (2*Real.pi)|/2:=by rw[abs_div,abs_of_pos (by norm_num:(0:ℝ)<2)]
    rw[hl1,hl2] at hu
    dsimp[C,b] at *
    linarith
lemma oddFactorial_log_identity (n:ℕ):
    Real.log (oddFactorial n:ℝ)=Real.log (2*(n:ℝ)+1)+Real.log ((2*n).factorial:ℝ)-
      (n:ℝ)*Real.log 2-Real.log (n.factorial:ℝ):=by
  have hi:(n.factorial:ℝ)*(oddFactorial n:ℝ)*2^n=((2*n+1).factorial:ℝ):=by
    have hnat:n.factorial*oddFactorial n*2^n=(2*n+1).factorial:=by exact_mod_cast oddFactorial_factorial n
    exact_mod_cast hnat
  have hfac:0<(n.factorial:ℝ):=by positivity
  have hodd:0<(oddFactorial n:ℝ):=by exact_mod_cast oddFactorial_pos n
  have hpow:0<(2:ℝ)^n:=by positivity
  have hlog:=congrArg Real.log hi
  rw[Real.log_mul (mul_pos hfac hodd).ne' hpow.ne',Real.log_mul hfac.ne' hodd.ne',Real.log_pow,
    Nat.factorial_succ,Nat.cast_mul,Real.log_mul (by positivity:((2*n+1:ℕ):ℝ)≠0) (by positivity:((2*n).factorial:ℝ)≠0)] at hlog
  push_cast at hlog
  linarith only[hlog]
lemma log_two_n_add_one_bound (n:ℕ):
    0≤Real.log (2*(n:ℝ)+1)∧Real.log (2*(n:ℝ)+1)≤2*Real.log ((n:ℝ)+1):=by
  have hn:0≤(n:ℝ):=Nat.cast_nonneg n
  refine ⟨Real.log_nonneg (by linarith),?_⟩
  have ht:2*(n:ℝ)+1≤((n:ℝ)+1)^2:=by nlinarith[sq_nonneg (n:ℝ)]
  have he:=Real.log_le_log (by positivity:0<2*(n:ℝ)+1) ht
  rwa[Real.log_pow] at he
lemma oddFactorial_log_uniform_bound:
    ∃C:ℝ,0<C∧∀n:ℕ,|Real.log (oddFactorial n:ℝ)-((n:ℝ)*Real.log (2*(n:ℝ))-n)|≤C*Real.log ((n:ℝ)+1):=by
  obtain ⟨C,hC,hfactor⟩:=factorial_log_uniform_bound
  refine ⟨3*C+2,by positivity,?_⟩
  intro n
  by_cases hn:n=0
  · subst n
    simp[oddFactorial]
  · have hnR:0<(n:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog:Real.log (2*(n:ℝ))=Real.log 2+Real.log (n:ℝ):=Real.log_mul (by norm_num) hnR.ne'
    have hid:Real.log (oddFactorial n:ℝ)-((n:ℝ)*Real.log (2*(n:ℝ))-n)=
        (Real.log ((2*n).factorial:ℝ)-((2*(n:ℝ))*Real.log (2*(n:ℝ))-2*n))-
          (Real.log (n.factorial:ℝ)-((n:ℝ)*Real.log (n:ℝ)-n))+Real.log (2*(n:ℝ)+1):=by
      rw[oddFactorial_log_identity,hlog]
      ring
    have h2:=hfactor (2*n)
    simp only[Nat.cast_mul,Nat.cast_ofNat] at h2
    have h1:=hfactor n
    have hlow:=log_two_n_add_one_bound n
    rw[hid]
    have ht:=abs_add_le
      ((Real.log ((2*n).factorial:ℝ)-((2*(n:ℝ))*Real.log (2*(n:ℝ))-2*n))-
        (Real.log (n.factorial:ℝ)-((n:ℝ)*Real.log (n:ℝ)-n))) (Real.log (2*(n:ℝ)+1))
    have hu:=abs_sub_le (Real.log ((2*n).factorial:ℝ)-((2*(n:ℝ))*Real.log (2*(n:ℝ))-2*n)) 0
      (Real.log (n.factorial:ℝ)-((n:ℝ)*Real.log (n:ℝ)-n))
    simp only[sub_zero,zero_sub,abs_neg] at hu
    have he:=mul_le_mul_of_nonneg_left hlow.2 hC.le
    rw[abs_of_nonneg hlow.1] at ht
    nlinarith
end WP.Coefficients
