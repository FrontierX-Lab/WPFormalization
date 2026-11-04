import WPFormalization.Analysis.FiniteExpGevreyTwo
import WPFormalization.HigherOrder.ComplexCoefficientAnalytic
/-! Finite exponential coefficients preserve a common complex Gevrey-two bound.
The exact finite coefficient formula is analytic in each input jet, restricts to the
real finiteExp operation, and is controlled by fixed Cauchy circles in the jet variable.
The physical complex domain is unchanged and constants precede every coefficient index. -/

noncomputable section
namespace WP.Analysis
open PowerSeries

def finiteExpComplex (f:PowerSeries ℂ) :PowerSeries ℂ:=
  PowerSeries.mk (fun n=>∑j∈Finset.range (n+1),PowerSeries.coeff n (f^j)/(j.factorial:ℂ))
def complexTruncatedSeriesPolynomial (f:PowerSeries ℂ) (K:ℕ) (z:ℂ):ℂ:=
  ∑j∈Finset.range (K+1),PowerSeries.coeff j f*z^j
lemma complexTruncatedSeriesPolynomial_analytic (f:PowerSeries ℂ) (K:ℕ) (z:ℂ):
    AnalyticAt ℂ (complexTruncatedSeriesPolynomial f K) z:=by
  unfold complexTruncatedSeriesPolynomial
  apply Finset.analyticAt_fun_sum
  intro j hj
  fun_prop
lemma complexTruncatedSeriesPolynomial_coeff (f:PowerSeries ℂ) (K n:ℕ):
    WP.coeff (complexTruncatedSeriesPolynomial f K) n=if n ≤ K then PowerSeries.coeff n f else 0:=by
  have ht:=taylor_finset_sum (Finset.range (K+1)) (fun j z=>PowerSeries.coeff j f*z^j) (by intro j hj;fun_prop)
  have hc:=congrArg (PowerSeries.coeff n) ht
  change WP.coeff (fun z=>∑j∈Finset.range (K+1),PowerSeries.coeff j f*z^j) n=_
  simpa only[taylor_coeff,map_sum,taylor_monomial,PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',
    Finset.mem_range,Nat.lt_succ_iff] using hc
lemma complexTruncatedSeriesPolynomial_zero (f:PowerSeries ℂ) (hf:PowerSeries.constantCoeff f=0) (K:ℕ):
    complexTruncatedSeriesPolynomial f K 0=0:=by
  have hc:=complexTruncatedSeriesPolynomial_coeff f K 0
  simpa only[WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,
    ite_eq_left (Nat.zero_le K),PowerSeries.coeff_zero_eq_constantCoeff,hf] using hc
lemma finiteExpComplex_truncated_polynomial_coeff (f:PowerSeries ℂ)
    (hf:PowerSeries.constantCoeff f=0) (K n:ℕ) (hn:n ≤ K):
    WP.coeff (fun z=>Complex.exp (complexTruncatedSeriesPolynomial f K z)) n=
      PowerSeries.coeff n (finiteExpComplex f):=by
  have he:∀i:ℕ,i ≤ K→PowerSeries.coeff i (taylor (complexTruncatedSeriesPolynomial f K))=PowerSeries.coeff i f:=by
    intro i hi
    rw[taylor_coeff,complexTruncatedSeriesPolynomial_coeff,ite_eq_left hi]
  rw[taylor_exp_coeff_finite _ (complexTruncatedSeriesPolynomial_analytic f K 0)
    (complexTruncatedSeriesPolynomial_zero f hf K)]
  simp only[finiteExpComplex,PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j hj
  rw[coeff_pow_eq_of_coeff_eq _ _ K he j n hn]

lemma complexTruncatedSeriesPolynomial_gevreyTwo_norm_bound (f:PowerSeries ℂ) (C B:ℝ)
    (hC:0 ≤ C) (hB:0<B) (hf:∀n,‖PowerSeries.coeff n f‖ ≤ C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ) (z:ℂ) (hz:‖z‖ ≤ 1/(2*B*((K:ℝ)+1)^2)) :
    ‖complexTruncatedSeriesPolynomial f K z‖ ≤ 2*C:=by
  have ht (n:ℕ) (hn:n∈Finset.range (K+1)):
      ‖PowerSeries.coeff n f*z^n‖ ≤ C*(1/(2:ℝ))^n:=by
    have hnK:n ≤ K:=by have hh:=Finset.mem_range.mp hn;omega
    rw[norm_mul,norm_pow]
    calc
      _ ≤ (C*B^n*(n.factorial:ℝ)^2)*(1/(2*B*((K:ℝ)+1)^2))^n:=
        mul_le_mul (hf n) (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity) (by positivity)
      _ ≤ (C*B^n*(((K:ℝ)+1)^2)^n)*(1/(2*B*((K:ℝ)+1)^2))^n:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (factorial_sq_le_order_pow n K hnK) (by positivity)) (by positivity)
      _=_:=by
        have he:B*((K:ℝ)+1)^2*(1/(2*B*((K:ℝ)+1)^2))=1/(2:ℝ):=by field_simp
        calc
          _=C*(B*((K:ℝ)+1)^2*(1/(2*B*((K:ℝ)+1)^2)))^n:=by simp only[mul_pow];ring
          _=_:=by rw[he]
  unfold complexTruncatedSeriesPolynomial
  calc
    _ ≤ ∑n∈Finset.range (K+1),‖PowerSeries.coeff n f*z^n‖:=norm_sum_le _ _
    _ ≤ ∑n∈Finset.range (K+1),C*(1/(2:ℝ))^n:=Finset.sum_le_sum ht
    _=C*(∑n∈Finset.range (K+1),(1/(2:ℝ))^n):=(Finset.mul_sum _ _ _).symm
    _ ≤ C*2:=mul_le_mul_of_nonneg_left (sum_geometric_two_le _) hC
    _=2*C:=by ring

lemma succ_order_pow_le_exp_factorial (n:ℕ):
    ((n:ℝ)+1)^n ≤ (2*Real.exp 1)^n*(n.factorial:ℝ):=by
  by_cases hn:n=0
  · subst n;simp
  have hnR:(1:ℝ) ≤ n:=by exact_mod_cast (show 1 ≤ n by omega)
  calc
    _ ≤ (2*(n:ℝ))^n:=pow_le_pow_left₀ (by positivity) (by linarith) _
    _=(2:ℝ)^n*(n:ℝ)^n:=mul_pow _ _ _
    _ ≤ (2:ℝ)^n*((Real.exp 1)^n*(n.factorial:ℝ)):=
      mul_le_mul_of_nonneg_left (order_pow_le_exp_factorial n) (by positivity)
    _=_:=by rw[mul_pow];ring

lemma finiteExpComplex_gevreyTwo_coeff_bound (f:PowerSeries ℂ) (C B:ℝ)
    (hC:0 ≤ C) (hB:0<B) (hf0:PowerSeries.constantCoeff f=0)
    (hf:∀n,‖PowerSeries.coeff n f‖ ≤ C*B^n*(n.factorial:ℝ)^2) (n:ℕ):
    ‖PowerSeries.coeff n (finiteExpComplex f)‖ ≤
      Real.exp (2*C)*(8*B*(Real.exp 1)^2)^n*(n.factorial:ℝ)^2:=by
  let R:ℝ:=1/(2*B*((n:ℝ)+1)^2)
  have hR:0<R:=by dsimp[R];positivity
  have hfun:DifferentiableOn ℂ (fun z=>Complex.exp (complexTruncatedSeriesPolynomial f n z))
      (Metric.closedBall 0 R):=by
    intro z hz
    exact ((Complex.hasDerivAt_exp _).comp z (complexTruncatedSeriesPolynomial_analytic f n z).differentiableAt.hasDerivAt).differentiableAt.differentiableWithinAt
  have hcircle:∀z∈Metric.sphere (0:ℂ) R,‖Complex.exp (complexTruncatedSeriesPolynomial f n z)‖ ≤ Real.exp (2*C):=by
    intro z hz
    have hzR:‖z‖ ≤ R:=by simpa only[Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hz
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr
      (complexTruncatedSeriesPolynomial_gevreyTwo_norm_bound f C B hC hB hf n z hzR))
  have hc:=coeff_norm_le_circle_bound (fun z=>Complex.exp (complexTruncatedSeriesPolynomial f n z)) R
    (Real.exp (2*C)) hR hfun hcircle n
  rw[finiteExpComplex_truncated_polynomial_coeff f hf0 n n le_rfl] at hc
  have hs:=pow_le_pow_left₀ (pow_nonneg (by positivity:(0:ℝ) ≤ (n:ℝ)+1) n)
    (succ_order_pow_le_exp_factorial n) 2
  have he:Real.exp (2*C)/R^n=
      Real.exp (2*C)*(2*B)^n*(((n:ℝ)+1)^n)^2:=by
    dsimp[R]
    rw[div_pow,one_pow,div_div_eq_mul_div,div_one,mul_pow]
    have hp:(((n:ℝ)+1)^2)^n=(((n:ℝ)+1)^n)^2:=by rw[←pow_mul,←pow_mul];congr 1;omega
    rw[hp]
    ring
  calc
    _ ≤ Real.exp (2*C)/R^n:=hc
    _=Real.exp (2*C)*(2*B)^n*(((n:ℝ)+1)^n)^2:=he
    _ ≤ Real.exp (2*C)*(2*B)^n*((2*Real.exp 1)^n*(n.factorial:ℝ))^2:=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _=_:=by
      have hp:((Real.exp 1)^2)^n=((Real.exp 1)^n)^2:=by rw[←pow_mul,←pow_mul];congr 1;omega
      have h8:(8:ℝ)^n=((2:ℝ)^n)^3:=by
        calc
          _=((2:ℝ)^3)^n:=by norm_num
          _=_:=by rw[←pow_mul,←pow_mul];congr 1;omega
      simp only[mul_pow,hp,h8]
      ring
lemma finiteExpComplex_coeff_of_real_jets (fc:PowerSeries ℂ) (fr:WP.HigherOrder.Series) (n:ℕ)
    (he:∀i:ℕ,i ≤ n→PowerSeries.coeff i fc=((PowerSeries.coeff i fr:ℝ):ℂ)) :
    PowerSeries.coeff n (finiteExpComplex fc)=((PowerSeries.coeff n (WP.HigherOrder.finiteExp fr):ℝ):ℂ):=by
  have he':∀i:ℕ,i ≤ n→PowerSeries.coeff i fc=PowerSeries.coeff i (PowerSeries.map Complex.ofRealHom fr):=by
    intro i hi
    rw[PowerSeries.coeff_map]
    exact he i hi
  simp only[finiteExpComplex,WP.HigherOrder.finiteExp,PowerSeries.coeff_mk,
    Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  rw[coeff_pow_eq_of_coeff_eq _ _ n he' j n le_rfl,←map_pow,PowerSeries.coeff_map]
  rfl

lemma finiteExpComplex_coeff_analyticOnNhd (Ω:Set ℂ) (f:ℂ→PowerSeries ℂ)
    (hf:∀n:ℕ,AnalyticOnNhd ℂ (fun z=>PowerSeries.coeff n (f z)) Ω) (n:ℕ) :
    AnalyticOnNhd ℂ (fun z=>PowerSeries.coeff n (finiteExpComplex (f z))) Ω:=by
  have hF:WP.HigherOrder.ComplexCanonical.AnalyticCoefficients Ω n f:=fun i hi=>hf i
  intro z hz
  simp only[finiteExpComplex,PowerSeries.coeff_mk]
  apply Finset.analyticAt_fun_sum
  intro j hj
  have hp : AnalyticAt ℂ (fun w:ℂ=>PowerSeries.coeff n ((f w)^j)) z := ((hF.pow j) n le_rfl) z hz
  simp only[div_eq_mul_inv]
  convert! hp.mul (analyticAt_const (v:=((j.factorial:ℂ)⁻¹))) using 1

lemma finiteExpComplex_family_gevreyTwo (Ω:Set ℂ) (f:ℂ→PowerSeries ℂ) (C B:ℝ)
    (hC:0 ≤ C) (hB:0<B)
    (hf0:∀z∈Ω,PowerSeries.constantCoeff (f z)=0)
    (ha:∀n:ℕ,AnalyticOnNhd ℂ (fun z=>PowerSeries.coeff n (f z)) Ω)
    (hf:∀n:ℕ,∀z∈Ω,‖PowerSeries.coeff n (f z)‖ ≤ C*B^n*(n.factorial:ℝ)^2) :
    (∀n:ℕ,AnalyticOnNhd ℂ (fun z=>PowerSeries.coeff n (finiteExpComplex (f z))) Ω) ∧
    (∀n:ℕ,∀z∈Ω,‖PowerSeries.coeff n (finiteExpComplex (f z))‖ ≤
      Real.exp (2*C)*(8*B*(Real.exp 1)^2)^n*(n.factorial:ℝ)^2):=by
  refine ⟨fun n=>finiteExpComplex_coeff_analyticOnNhd Ω f ha n,?_⟩
  intro n z hz
  exact finiteExpComplex_gevreyTwo_coeff_bound (f z) C B hC hB (hf0 z hz) (fun i=>hf i z hz) n

end WP.Analysis
