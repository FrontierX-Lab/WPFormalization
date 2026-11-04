import Mathlib
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma analytic_log1p_second_remainder:
    ∃L:ℂ→ℂ,AnalyticAt ℂ L 0∧∀ᶠt:ℂ in 𝓝 0,Complex.log (1+t)-t=t^2*L t:=by
  let F:ℂ→ℂ:=fun t=>Complex.log (1+t)-t
  have hplane:(1+(0:ℂ))∈Complex.slitPlane:=Or.inl (by norm_num)
  have hF:AnalyticAt ℂ F 0:=((analyticAt_const.add analyticAt_id).clog hplane).sub analyticAt_id
  have hzero:F 0=0:=by simp[F]
  have hderiv:deriv F 0=0:=by
    have hh:=(((hasDerivAt_const (0:ℂ) (1:ℂ)).add (hasDerivAt_id 0)).clog hplane).sub (hasDerivAt_id 0)
    simpa only[Pi.sub_def,Pi.add_apply,id_eq,zero_add,add_zero,one_div,inv_one,sub_self,F] using hh.deriv
  obtain ⟨L,hL,he⟩:=hF.exists_eventuallyEq_sum_add_pow_mul 2
  refine ⟨L,hL,?_⟩
  filter_upwards[he] with t ht
  simpa only[Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,iteratedDeriv_zero,iteratedDeriv_one,
    hzero,hderiv,smul_eq_mul,mul_zero,zero_mul,add_zero,zero_add,F,Complex.log_one,sub_zero,one_mul] using ht
end WP.Analysis
