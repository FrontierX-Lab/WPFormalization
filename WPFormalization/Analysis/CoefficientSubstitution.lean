import WPFormalization.Analysis.Taylor
import Mathlib.Analysis.Analytic.Order
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma coeff_id_pow_mul (f:ℂ → ℂ) (hf:AnalyticAt ℂ f 0) (n k:ℕ):
    WP.coeff (fun u:ℂ=>u^n*f u) k=if n≤k then WP.coeff f (k-n) else 0:=by
  have he:=congrArg (PowerSeries.coeff k)
    (taylor_mul (f:=fun u:ℂ=>u^n) (g:=f) (by fun_prop) hf)
  have hp:taylor (fun u:ℂ=>u^n)=(PowerSeries.X:PowerSeries ℂ)^n:=by
    rw[taylor_pow (f:=fun u:ℂ=>u) analyticAt_id n,taylor_id]
  rw[hp,PowerSeries.coeff_X_pow_mul'] at he
  simpa only[taylor_coeff] using he
lemma coeff_complex_euler (f:ℂ → ℂ) (hf:AnalyticAt ℂ f 0) (k:ℕ):
    WP.coeff (fun u:ℂ=>u*deriv f u) k=(k:ℂ)*WP.coeff f k:=by
  have he:=congrArg (PowerSeries.coeff k) (taylor_euler hf)
  cases k with
  | zero=>simpa using he
  | succ k=>simpa only[taylor_coeff,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_derivative,Nat.cast_add,Nat.cast_one,mul_comm] using he
lemma coeff_sub_euler_div (f:ℂ → ℂ) (hf:AnalyticAt ℂ f 0) (k:ℕ) (hk:k≠0):
    WP.coeff (fun u:ℂ=>f u-u*deriv f u/(k:ℂ)) k=0:=by
  have he:=congrArg (PowerSeries.coeff k)
    (taylor_sub (f:=f) (g:=fun u:ℂ=>(k:ℂ)⁻¹*(u*deriv f u)) hf
      (analyticAt_const.mul (analyticAt_id.mul hf.deriv)))
  simp only[taylor_coeff,map_sub,taylor_const_mul,PowerSeries.coeff_C_mul] at he
  have hkn:(k:ℂ)≠0:=by exact_mod_cast hk
  convert he.trans ?_ using 2
  · funext u;ring
  · rw[coeff_complex_euler f hf k]
    field_simp <;> ring
end WP.Analysis


namespace WP.Analysis
lemma hasDerivAt_inv_pow (q:ℂ → ℂ) (u:ℂ) (hq:DifferentiableAt ℂ q u) (hqu:q u≠0) (m:ℕ):
    HasDerivAt (fun z:ℂ=>(q z)⁻¹^m) (-(m:ℂ)*deriv q u/(q u)^(m+1)) u:=by
  have hd:=(hq.hasDerivAt.inv hqu).pow m
  convert! hd using 1
  by_cases hm:m=0
  · subst m;simp
  · obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hm
    simp only[Nat.succ_sub_one,Pi.inv_apply,inv_pow,pow_succ]
    field_simp <;> ring
end WP.Analysis


namespace WP.Analysis
lemma monomial_substitution_lower_algebra (a b u:ℂ) (ha:a≠0) (n m:ℕ) (hm:(m:ℂ)≠0):
    (u*a)^n*(a+u*b)/a^(n+m+1)=
      u^n*((a⁻¹)^m-u*(-(m:ℂ)*b/a^(m+1))/(m:ℂ)):=by
  simp only[mul_pow,inv_pow,pow_add,pow_one]
  field_simp <;> ring
lemma monomial_substitution_equal_algebra (a b u:ℂ) (ha:a≠0) (n:ℕ):
    (u*a)^n*(a+u*b)/a^(n+1)=u^n*(1+u*b/a):=by
  simp only[mul_pow,pow_add,pow_one]
  field_simp <;> ring
end WP.Analysis

namespace WP.Analysis
open Filter
open scoped Topology
lemma coeff_monomial_coordinate_substitution (q:ℂ → ℂ) (hq:AnalyticAt ℂ q 0)
    (hq0:q 0≠0) (n k:ℕ) (hn:n≤k):
    WP.coeff (fun u:ℂ=>(u*q u)^n*(q u+u*deriv q u)/(q u)^(k+1)) k=
      if n=k then 1 else 0:=by
  have hqnear:∀ᶠu:ℂ in 𝓝 0,q u≠0:=hq.continuousAt.eventually (eventually_ne_nhds hq0)
  by_cases hnk:n=k
  · subst n
    have he:(fun u:ℂ=>(u*q u)^k*(q u+u*deriv q u)/(q u)^(k+1))=ᶠ[𝓝 0]
        (fun u:ℂ=>u^k*(1+u*deriv q u/q u)):=by
      filter_upwards[hqnear] with u hu
      exact monomial_substitution_equal_algebra (q u) (deriv q u) u hu k
    have ha:AnalyticAt ℂ (fun u:ℂ=>1+u*deriv q u/q u) 0:=
      analyticAt_const.add ((analyticAt_id.mul hq.deriv).div hq hq0)
    have hc:=congrArg (PowerSeries.coeff k) (taylor_congr he)
    simp only[taylor_coeff] at hc
    rw[hc,coeff_id_pow_mul _ ha,if_pos (le_refl k),Nat.sub_self]
    simp [WP.coeff]

  · let m:=k-n
    have hm:m≠0:=by dsimp[m];omega
    have hmn:(m:ℂ)≠0:=by exact_mod_cast hm
    let f:ℂ → ℂ:=fun u=>(q u)⁻¹^m
    have hf:AnalyticAt ℂ f 0:=(hq.inv hq0).pow m
    have he:(fun u:ℂ=>(u*q u)^n*(q u+u*deriv q u)/(q u)^(k+1))=ᶠ[𝓝 0]
        (fun u:ℂ=>u^n*(f u-u*deriv f u/(m:ℂ))):=by
      filter_upwards[hqnear,hq.eventually_analyticAt] with u hu hqu
      have hd:deriv f u=-(m:ℂ)*deriv q u/(q u)^(m+1):=
        (hasDerivAt_inv_pow q u hqu.differentiableAt hu m).deriv
      rw[hd]
      have hkm:k=n+m:=by dsimp[m];omega
      rw[hkm]
      exact monomial_substitution_lower_algebra (q u) (deriv q u) u hu n m hmn
    have ha:AnalyticAt ℂ (fun u:ℂ=>f u-u*deriv f u/(m:ℂ)) 0:=
      hf.sub ((analyticAt_id.mul hf.deriv).div_const)
    have hc:=congrArg (PowerSeries.coeff k) (taylor_congr he)
    simp only[taylor_coeff] at hc
    rw[hc,coeff_id_pow_mul _ ha,if_pos hn,if_neg hnk]
    exact coeff_sub_euler_div f hf (k-n) hm

end WP.Analysis

namespace WP.Analysis
open Filter
open scoped Topology
lemma coeff_finite_sum {ι:Type*} (s:Finset ι) (f:ι → ℂ → ℂ)
    (hf:∀i∈s,AnalyticAt ℂ (f i) 0) (k:ℕ):
    WP.coeff (fun u:ℂ=>∑i∈s,f i u) k=∑i∈s,WP.coeff (f i) k:=by
  simp only[WP.coeff]
  rw[iteratedDeriv_fun_sum (fun i hi=>(hf i hi).contDiffAt),Finset.sum_div]
lemma coeff_const_mul (c:ℂ) (f:ℂ → ℂ) (k:ℕ):
    WP.coeff (fun u:ℂ=>c*f u) k=c*WP.coeff f k:=by
  have he:=congrArg (PowerSeries.coeff k) (taylor_const_mul c f)
  simpa only[taylor_coeff,PowerSeries.coeff_C_mul] using he
lemma coeff_analytic_coordinate_substitution (G q:ℂ → ℂ)
    (hG:AnalyticAt ℂ G 0) (hq:AnalyticAt ℂ q 0) (hq0:q 0≠0) (k:ℕ):
    WP.coeff (fun u:ℂ=>G (u*q u)*(q u+u*deriv q u)/(q u)^(k+1)) k=WP.coeff G k:=by
  obtain ⟨R,hR,hTaylor⟩:=hG.exists_eventuallyEq_sum_add_pow_mul (k+1)
  let Z:ℂ → ℂ:=fun u=>u*q u
  have hZ:AnalyticAt ℂ Z 0:=analyticAt_id.mul hq
  have hZ0:Z 0=0:=by simp[Z]
  have hZt:Tendsto Z (𝓝 0) (𝓝 0):=by simpa only[hZ0] using hZ.continuousAt.tendsto
  let D:ℂ → ℂ:=fun u=>q u+u*deriv q u
  have hD:AnalyticAt ℂ D 0:=hq.add (analyticAt_id.mul hq.deriv)
  let term:ℕ → ℂ → ℂ:=fun i u=>WP.coeff G i*((u*q u)^i*D u/(q u)^(k+1))
  have hterm(i:ℕ):AnalyticAt ℂ (term i) 0:=analyticAt_const.mul
    (((hZ.pow i).mul hD).div (hq.pow (k+1)) (pow_ne_zero _ hq0))
  let T:ℂ → ℂ:=fun u=>(q u)^(k+1)*R (Z u)*D u/(q u)^(k+1)
  have hRc:AnalyticAt ℂ (fun u:ℂ=>R (Z u)) 0:=by
    have hh:AnalyticAt ℂ R (Z 0):=by rw[hZ0];exact hR
    exact hh.comp (f:=Z) hZ
  have hT:AnalyticAt ℂ T 0:=(((hq.pow (k+1)).mul hRc).mul hD).div
    (hq.pow (k+1)) (pow_ne_zero _ hq0)
  have he:(fun u:ℂ=>G (Z u)*D u/(q u)^(k+1))=ᶠ[𝓝 0]
      (fun u:ℂ=>(∑i∈Finset.range (k+1),term i u)+u^(k+1)*T u):=by
    filter_upwards[hZt.eventually hTaylor] with u hu
    rw[hu]
    simp only[smul_eq_mul,add_mul,add_div,Finset.sum_mul,Finset.sum_div]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      dsimp[term,WP.coeff,Z]
      ring
    · dsimp[T,Z]
      rw[mul_pow]
      ring
  have hc:=congrArg (PowerSeries.coeff k) (taylor_congr he)
  simp only[taylor_coeff] at hc
  have hasum:AnalyticAt ℂ (fun u:ℂ=>∑i∈Finset.range (k+1),term i u) 0:=
    Finset.analyticAt_fun_sum _ (fun i hi=>hterm i)
  have haR:AnalyticAt ℂ (fun u:ℂ=>u^(k+1)*T u) 0:=(analyticAt_id.pow (k+1)).mul hT
  have hadd:=congrArg (PowerSeries.coeff k) (taylor_add hasum haR)
  simp only[taylor_coeff,map_add] at hadd
  rw[hadd,coeff_id_pow_mul T hT,if_neg (by omega:¬k+1≤k),add_zero,
    coeff_finite_sum _ _ (fun i hi=>hterm i)] at hc
  calc
    _=∑i∈Finset.range (k+1),WP.coeff (term i) k:=hc
    _=∑i∈Finset.range (k+1),WP.coeff G i*(if i=k then 1 else 0):=by
      apply Finset.sum_congr rfl
      intro i hi
      rw[coeff_const_mul]
      congr 1
      exact coeff_monomial_coordinate_substitution q hq hq0 i k
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _=WP.coeff G k:=by simp
end WP.Analysis
