import WPFormalization.Analysis.GammaLaplaceKernel
import Mathlib.NumberTheory.BernoulliPolynomials
/-! The actual removable Laplace kernel has exactly the prescribed Bernoulli
formal log-Gamma coefficients. Only finite coefficient algebra and analytic
Taylor identities are used; no asymptotic Gamma input is invoked. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder

lemma bernoulliPolynomialValue_eq_eval (n : ℕ) (a : ℚ) :
    bernoulliPolynomialValue n a=(Polynomial.bernoulli n).eval a := by
  unfold bernoulliPolynomialValue Polynomial.bernoulli
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_monomial]
  ring

end WP.HigherOrder
namespace WP.Analysis
open PowerSeries Filter
open scoped Topology

lemma taylor_exp_const_mul (c : ℂ) :
    taylor (fun z=>Complex.exp (c*z))=PowerSeries.rescale c (PowerSeries.exp ℂ) := by
  ext n
  simp only [taylor_coeff,WP.coeff,iteratedDeriv_cexp_const_mul,mul_zero,Complex.exp_zero,mul_one,
    PowerSeries.coeff_rescale,PowerSeries.coeff_exp,map_inv₀,map_natCast,one_div]
  ring

lemma complexExpUnit_mul_arg (z : ℂ) : z*complexExpUnit z=Complex.exp z-1 := by
  simpa only [sub_zero,smul_eq_mul,Complex.exp_zero,complexExpUnit] using sub_smul_dslope Complex.exp 0 z

lemma gammaRatioKernel_mul_arg (a : ℝ) (z : ℂ) : z*gammaRatioKernel a z=(a:ℂ)-gammaRatioQuotient a z := by
  have h := sub_smul_dslope (gammaRatioQuotient a) 0 z
  simp only [sub_zero,smul_eq_mul,gammaRatioQuotient_zero] at h
  unfold gammaRatioKernel
  linear_combination -h

private lemma rat_complex_algebraMap (q : ℚ) : (algebraMap ℚ ℂ) q=(q:ℂ) :=
  congrArg (fun f : ℚ →+* ℂ=>f q) (Subsingleton.elim _ (Rat.castHom ℂ))

def gammaBernoulliSeries (a : ℚ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n=>Polynomial.aeval ((algebraMap ℚ ℂ) a) ((1/(n.factorial:ℚ)) • Polynomial.bernoulli n))

lemma gammaBernoulliSeries_generating (a : ℚ) :
    gammaBernoulliSeries a*(PowerSeries.exp ℂ-1)=PowerSeries.X*PowerSeries.rescale (a:ℂ) (PowerSeries.exp ℂ) :=
  by
    simpa only [gammaBernoulliSeries,rat_complex_algebraMap] using Polynomial.bernoulli_generating_function ((algebraMap ℚ ℂ) a)

lemma gammaBernoulliSeries_coeff (a : ℚ) (n : ℕ) :
    PowerSeries.coeff n (gammaBernoulliSeries a)=
      ((WP.HigherOrder.bernoulliPolynomialValue n a:ℚ):ℂ)/(n.factorial:ℂ) := by
  rw [gammaBernoulliSeries,PowerSeries.coeff_mk,Polynomial.aeval_def,Polynomial.eval₂_at_apply]
  simp only [Polynomial.eval_smul,smul_eq_mul,map_mul,map_div₀,map_one,map_natCast,rat_complex_algebraMap]
  rw [← WP.HigherOrder.bernoulliPolynomialValue_eq_eval]
  ring


lemma gammaRatioQuotient_exp_eventually (a : ℝ) :
    (fun z=>gammaRatioQuotient a z*(1-Complex.exp (-z))) =ᶠ[𝓝 0]
      (fun z=>1-Complex.exp (-(a:ℂ)*z)) := by
  have hc : ContinuousAt (fun z:ℂ=>complexExpUnit (-z)) 0 := by fun_prop
  have h0 : complexExpUnit (-(0:ℂ))≠0 := by simp
  filter_upwards [hc.eventually_ne h0] with z hz
  have h1 := complexExpUnit_mul_arg (-z)
  have h2 := complexExpUnit_mul_arg (-(a:ℂ)*z)
  have hd : 1-Complex.exp (-z)=z*complexExpUnit (-z) := by linear_combination h1
  have hn : 1-Complex.exp (-(a:ℂ)*z)=z*((a:ℂ)*complexExpUnit (-(a:ℂ)*z)) := by
    linear_combination h2
  rw [hd,hn,gammaRatioQuotient]
  field_simp [hz]

lemma taylor_one_sub_exp_const_mul (c : ℂ) :
    taylor (fun z=>1-Complex.exp (c*z))=1-PowerSeries.rescale c (PowerSeries.exp ℂ) := by
  rw [taylor_sub analyticAt_const (by fun_prop),taylor_const,taylor_exp_const_mul,map_one]

lemma gammaRatioQuotient_taylor_exp_identity (a : ℝ) :
    taylor (gammaRatioQuotient a)*(1-PowerSeries.rescale (-1) (PowerSeries.exp ℂ))=
      1-PowerSeries.rescale (-(a:ℂ)) (PowerSeries.exp ℂ) := by
  have hd : taylor (fun z:ℂ=>1-Complex.exp (-z))=1-PowerSeries.rescale (-1) (PowerSeries.exp ℂ) := by
    simpa only [neg_one_mul] using taylor_one_sub_exp_const_mul (-1)
  calc
    _ = taylor (fun z=>gammaRatioQuotient a z*(1-Complex.exp (-z))) := by
      rw [taylor_mul (gammaRatioQuotient_analytic_zero a) (by fun_prop),hd]
    _ = taylor (fun z=>1-Complex.exp (-(a:ℂ)*z)) := taylor_congr (gammaRatioQuotient_exp_eventually a)
    _ = _ := taylor_one_sub_exp_const_mul _

lemma gammaRatioKernel_taylor_identity (a : ℝ) :
    PowerSeries.X*taylor (gammaRatioKernel a)=PowerSeries.C (a:ℂ)-taylor (gammaRatioQuotient a) := by
  calc
    _ = taylor (fun z=>z*gammaRatioKernel a z) := by
      rw [taylor_mul (f:=fun z:ℂ=>z) (g:=gammaRatioKernel a) analyticAt_id (gammaRatioKernel_analytic_zero a),taylor_id]
    _ = taylor (fun z=>(a:ℂ)-gammaRatioQuotient a z) :=
      taylor_congr (Filter.Eventually.of_forall (gammaRatioKernel_mul_arg a))
    _ = _ := by rw [taylor_sub analyticAt_const (gammaRatioQuotient_analytic_zero a),taylor_const]

lemma gammaBernoulliSeries_neg_generating (a : ℚ) :
    PowerSeries.rescale (-1) (gammaBernoulliSeries a)*(1-PowerSeries.rescale (-1) (PowerSeries.exp ℂ))=
      PowerSeries.X*PowerSeries.rescale (-(a:ℂ)) (PowerSeries.exp ℂ) := by
  have hs := congrArg (PowerSeries.rescale (-1:ℂ)) (gammaBernoulliSeries_generating a)
  simp only [map_mul,map_sub,map_one,PowerSeries.rescale_X,PowerSeries.rescale_rescale,
    mul_neg_one,map_neg,neg_one_mul] at hs
  linear_combination -hs

lemma gammaRatioQuotient_bernoulli_identity (a : ℚ) :
    PowerSeries.X*taylor (gammaRatioQuotient (a:ℝ))=
      PowerSeries.rescale (-1) (gammaBernoulliSeries 0)-PowerSeries.rescale (-1) (gammaBernoulliSeries a) := by
  let D : PowerSeries ℂ := 1-PowerSeries.rescale (-1) (PowerSeries.exp ℂ)
  have hD : D≠0 := by
    intro hd
    have he := congrArg (PowerSeries.coeff 1) hd
    norm_num [D,PowerSeries.coeff_rescale,PowerSeries.coeff_exp] at he
  apply mul_right_cancel₀ hD
  have hQ := gammaRatioQuotient_taylor_exp_identity (a:ℝ)
  simp only [Complex.ofReal_ratCast] at hQ
  calc
    (PowerSeries.X*taylor (gammaRatioQuotient (a:ℝ)))*D=
        PowerSeries.X*(1-PowerSeries.rescale (-(a:ℂ)) (PowerSeries.exp ℂ)) := by
      rw [mul_assoc]
      exact congrArg (fun f=>PowerSeries.X*f) hQ
    _ = _ := by
      rw [sub_mul,gammaBernoulliSeries_neg_generating 0,gammaBernoulliSeries_neg_generating a]
      simp only [Rat.cast_zero,neg_zero,PowerSeries.rescale_zero_apply,PowerSeries.constantCoeff_exp,map_one,mul_one]
      ring


lemma gammaRatioKernel_coeff_bernoulli (a : ℚ) (n : ℕ) :
    WP.coeff (gammaRatioKernel (a:ℝ)) n=
      (-1:ℂ)^(n+2)*(((WP.HigherOrder.bernoulliPolynomialValue (n+2) a-
        WP.HigherOrder.bernoulliPolynomialValue (n+2) 0:ℚ):ℂ))/( (n+2).factorial:ℂ) := by
  have hq := congrArg (PowerSeries.coeff (n+1+1)) (gammaRatioQuotient_bernoulli_identity a)
  simp only [PowerSeries.coeff_succ_X_mul,map_sub,PowerSeries.coeff_rescale,gammaBernoulliSeries_coeff,taylor_coeff] at hq
  have hk := congrArg (PowerSeries.coeff (n+1)) (gammaRatioKernel_taylor_identity (a:ℝ))
  simp only [PowerSeries.coeff_succ_X_mul,map_sub,PowerSeries.coeff_C,
    ite_eq_right (show n+1≠0 by omega),zero_sub,taylor_coeff] at hk
  rw [hq] at hk
  push_cast
  convert! hk using 1 <;>ring

lemma gammaRatioKernel_coeff_log (a : ℚ) (n : ℕ) :
    WP.coeff (gammaRatioKernel (a:ℝ)) n*(n.factorial:ℂ)=
      ((PowerSeries.coeff (n+1) (WP.HigherOrder.gammaRatioLog a):ℝ):ℂ) := by
  rw [gammaRatioKernel_coeff_bernoulli]
  simp only [WP.HigherOrder.gammaRatioLog,PowerSeries.coeff_mk,
    ite_eq_right (show n+1≠0 by omega)]
  push_cast
  rw [Nat.factorial_succ,Nat.factorial_succ]
  push_cast
  have hf : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  have hn1 : (n:ℂ)+1≠0 := by exact_mod_cast (show n+1≠0 by omega)
  have hn2 : (n:ℂ)+2≠0 := by exact_mod_cast (show n+2≠0 by omega)
  field_simp [hf,hn1,hn2]

end WP.Analysis
