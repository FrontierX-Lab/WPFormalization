import WPFormalization.HigherOrder.Extraction
import WPFormalization.HigherOrder.BernoulliCoefficientBounds
import WPFormalization.Analysis.GevreyOneMatching
import WPFormalization.External.SpecialFunctions
/-! The logarithm of the exact Poisson normalizer matches the original
Bernoulli series, with an error uniform in every order. The sole deferred input
is the registered positive-real Binet/Stirling remainder. -/
noncomputable section
namespace WP.Analysis
open PowerSeries
open WP.HigherOrder

def poissonLogNormalizer (x:ℝ):ℝ:=
  - (Real.log (Real.Gamma x) - ((x-1/2)*Real.log x-x+Real.log (2*Real.pi)/2))

lemma poissonStirlingLog_even (m:ℕ):
    PowerSeries.coeff (2*m) poissonStirlingLog=0:=by
  have hn:¬Odd (2*m):=by rintro ⟨k,hk⟩;omega
  simp[poissonStirlingLog,hn]

lemma poissonStirlingLog_odd (m:ℕ):
    PowerSeries.coeff (2*m+1) poissonStirlingLog=
      -(bernoulli (2*(m+1)):ℝ)/(((2*(m+1):ℕ):ℝ)*((2*(m+1)-1:ℕ):ℝ)):=by
  have hn:Odd (2*m+1):=⟨m,by omega⟩
  simp only[poissonStirlingLog,PowerSeries.coeff_mk,ite_eq_left hn]
  rw [show 2*m+1+1=2*(m+1) by omega]
  rw [show 2*(m+1)-1=2*m+1 by omega]
  congr 1
  push_cast
  ring

lemma poissonStirlingLog_partial (m:ℕ)(x:ℝ):
    inversePowerTruncation poissonStirlingLog (2*m) x=
      -(∑k∈Finset.Icc 1 m,(bernoulli (2*k):ℝ)/
        (((2*k:ℕ):ℝ)*((2*k-1:ℕ):ℝ)*x^(2*k-1))):=by
  induction m with
  | zero=>simp[inversePowerTruncation,poissonStirlingLog]
  | succ m ih=>
    have hsum:inversePowerTruncation poissonStirlingLog (2*(m+1)) x=
        inversePowerTruncation poissonStirlingLog (2*m) x+
          PowerSeries.coeff (2*m+1) poissonStirlingLog/x^(2*m+1):=by
      unfold inversePowerTruncation
      rw[show 2*(m+1)+1=(2*m+1)+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ]
      rw[show 2*m+1+1=2*(m+1) by omega,poissonStirlingLog_even]
      simp
    rw[hsum,ih,Finset.sum_Icc_succ_top (by omega : 1 ≤ m+1),poissonStirlingLog_odd]
    rw [show 2*(m+1)-1=2*m+1 by omega]
    ring

lemma poissonStirlingLog_rounded_partial (K:ℕ)(x:ℝ):
    inversePowerTruncation poissonStirlingLog (2*((K+1)/2)) x=
      inversePowerTruncation poissonStirlingLog K x:=by
  have hk:K≤2*((K+1)/2) ∧ 2*((K+1)/2)≤K+1:=by omega
  by_cases he:2*((K+1)/2)=K
  · rw[he]
  · have he':2*((K+1)/2)=K+1:=by omega
    have hzero:PowerSeries.coeff (K+1) poissonStirlingLog=0:=by
      rw[←he',poissonStirlingLog_even]
    unfold inversePowerTruncation
    rw[he',Finset.sum_range_succ,hzero,zero_div,add_zero]

lemma bernoulli_stirling_omitted_bound (m:ℕ):
    |(bernoulli (2*(m+1)):ℝ)| /
      (((2*(m+1):ℕ):ℝ)*((2*(m+1)-1:ℕ):ℝ))≤
      (2:ℝ)^(2*m+2)*((2*m).factorial:ℝ):=by
  have hb:|(bernoulli (2*m+2):ℝ)|≤(2:ℝ)^(2*m+2)*((2*m+2).factorial:ℝ):=by
    exact_mod_cast bernoulli_factorial_bound (2*m+2)
  rw[show 2*(m+1)=2*m+2 by omega,show 2*m+2-1=2*m+1 by omega]
  apply (div_le_iff₀ (by positivity)).mpr
  apply hb.trans_eq
  rw[show 2*m+2=(2*m+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
  push_cast
  ring

lemma poissonLogNormalizer_uniform_error (K:ℕ)(x:ℝ)(hx:1≤x):
    |poissonLogNormalizer x-inversePowerTruncation poissonStirlingLog K x|≤
      4*(2:ℝ)^(K+1)*((K+1).factorial:ℝ)/x^(K+1):=by
  let m:ℕ:=(K+1)/2
  have hlow:K≤2*m:=by dsimp[m];omega
  have hupp:2*m≤K+1:=by dsimp[m];omega
  have hx0:0<x:=zero_lt_one.trans_le hx
  have hclass:=External.log_gamma_stirling_remainder (m+1) (by omega) x hx0
  have hpartial:poissonLogNormalizer x-inversePowerTruncation poissonStirlingLog K x=
      -(Real.log (Real.Gamma x)-External.logStirlingPartial (m+1) x):=by
    rw[←poissonStirlingLog_rounded_partial K x]
    change poissonLogNormalizer x-inversePowerTruncation poissonStirlingLog (2*m) x=_
    rw[poissonStirlingLog_partial]
    simp only[External.logStirlingPartial,Nat.add_sub_cancel,poissonLogNormalizer]
    ring
  rw[hpartial,abs_neg]
  apply hclass.trans
  rw[show 2*(m+1)-1=2*m+1 by omega,←div_div]
  calc
    _ ≤ ((2:ℝ)^(2*m+2)*((2*m).factorial:ℝ))/x^(2*m+1):=
      div_le_div_of_nonneg_right (bernoulli_stirling_omitted_bound m) (by positivity)
    _ ≤ ((2:ℝ)^(K+3)*((K+1).factorial:ℝ))/x^(K+1):=by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega))
          (by exact_mod_cast Nat.factorial_le hupp) (by positivity) (by positivity)
      · positivity
      · exact pow_le_pow_right₀ hx (by omega)
    _ = _:=by rw[show K+3=(K+1)+2 by omega,pow_add];ring

lemma poissonLogNormalizer_gevrey_one:
    GevreyOneAsymptotic poissonLogNormalizer poissonStirlingLog:=by
  refine ⟨4,2,1,1,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
  intro K x hx _
  exact poissonLogNormalizer_uniform_error K x hx
end WP.Analysis
