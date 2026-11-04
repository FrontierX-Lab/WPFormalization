import WPFormalization.Analysis.PoissonPhaseAlgebra
import WPFormalization.Analysis.ParameterInverse
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
noncomputable section
namespace WP.Analysis
lemma iteratedDeriv_two_clog (z:ℂ) (hz:z∈Complex.slitPlane):
    iteratedDeriv 2 Complex.log z=-(z⁻¹)^2:=by
  have hh:=iteratedDeriv_succ_log (n:=1) hz
  norm_num[zpow_neg] at hh ⊢
  exact hh
lemma poisson_phase_second_derivative (S z:ℂ→ℂ) (ν u:ℂ)
    (hS:AnalyticAt ℂ S (z u)) (hz:AnalyticAt ℂ z u)
    (hzu:z u∈Complex.slitPlane) (hu:u∈Complex.slitPlane):
    iteratedDeriv 2 (fun w:ℂ=>S (z w)-w-ν*Complex.log (z w)+ν*Complex.log w) u=
      (iteratedDeriv 2 S (z u)+ν*(z u)⁻¹^2)*(deriv z u)^2+
        (deriv S (z u)-ν/(z u))*iteratedDeriv 2 z u-ν*u⁻¹^2:=by
  have hSc:AnalyticAt ℂ (fun w:ℂ=>S (z w)) u:=hS.comp (f:=z) hz
  have hLc:AnalyticAt ℂ (fun w:ℂ=>Complex.log (z w)) u:=
    (analyticAt_clog hzu).comp (f:=z) hz
  have hA:AnalyticAt ℂ (fun w:ℂ=>S (z w)-w) u:=hSc.sub analyticAt_id
  have hB:AnalyticAt ℂ (fun w:ℂ=>ν*Complex.log (z w)) u:=analyticAt_const.mul hLc
  have hC:AnalyticAt ℂ (fun w:ℂ=>ν*Complex.log w) u:=analyticAt_const.mul (analyticAt_clog hu)
  rw[iteratedDeriv_fun_add (f:=fun w:ℂ=>S (z w)-w-ν*Complex.log (z w))
      (g:=fun w:ℂ=>ν*Complex.log w) (hA.sub hB).contDiffAt hC.contDiffAt,
    iteratedDeriv_fun_sub (f:=fun w:ℂ=>S (z w)-w) (g:=fun w:ℂ=>ν*Complex.log (z w)) hA.contDiffAt hB.contDiffAt,
    iteratedDeriv_fun_sub (f:=fun w:ℂ=>S (z w)) (g:=fun w:ℂ=>w) hSc.contDiffAt (by fun_prop),
    iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
  have heS:iteratedDeriv 2 (fun w:ℂ=>S (z w)) u=
      iteratedDeriv 2 S (z u)*(deriv z u)^2+deriv S (z u)*iteratedDeriv 2 z u:=by
    simpa only[Function.comp_def] using iteratedDeriv_comp_two hS.contDiffAt hz.contDiffAt
  have heL:iteratedDeriv 2 (fun w:ℂ=>Complex.log (z w)) u=
      iteratedDeriv 2 Complex.log (z u)*(deriv z u)^2+deriv Complex.log (z u)*iteratedDeriv 2 z u:=by
    simpa only[Function.comp_def] using iteratedDeriv_comp_two (analyticAt_clog hzu).contDiffAt hz.contDiffAt
  rw[heS,heL,iteratedDeriv_two_clog _ hzu,iteratedDeriv_two_clog _ hu,Complex.deriv_log hzu]
  have hi:iteratedDeriv 2 (fun w:ℂ=>w) u=0:=by simp[iteratedDeriv_succ]
  rw[hi]
  simp only[div_eq_mul_inv]
  ring
end WP.Analysis
namespace WP.Analysis
open Filter
open scoped Topology
lemma log_div_positive_real_germ (z:ℂ→ℂ) (ν x:ℝ) (hν:0<ν) (hx:0<x)
    (hz:AnalyticAt ℂ z (ν:ℂ)) (hzv:z (ν:ℂ)=(x:ℂ)):
    ∀ᶠu:ℂ in 𝓝 (ν:ℂ),Complex.log (z u/u)=Complex.log (z u)-Complex.log u:=by
  have hn:(ν:ℂ)≠0:=by exact_mod_cast hν.ne'
  have hqr:0<(z (ν:ℂ)/(ν:ℂ)).re:=by
    rw[hzv,←Complex.ofReal_div,Complex.ofReal_re]
    exact div_pos hx hν
  have hqc:ContinuousAt (fun u:ℂ=>(z u/u).re) (ν:ℂ):=
    Complex.continuous_re.continuousAt.comp (f:=fun u:ℂ=>z u/u) (hz.continuousAt.div continuousAt_id hn)
  have hure:∀ᶠu:ℂ in 𝓝 (ν:ℂ),0<u.re:=
    Complex.continuous_re.continuousAt.tendsto.eventually (eventually_gt_nhds (by simpa only[Complex.ofReal_re] using hν))
  have hqre:∀ᶠu:ℂ in 𝓝 (ν:ℂ),0<(z u/u).re:=hqc.tendsto.eventually (eventually_gt_nhds hqr)
  filter_upwards[hure,hqre] with u hu hq
  have hun:u≠0:=by intro h;rw[h,Complex.zero_re] at hu;exact (lt_irrefl _ hu)
  have he:u*(z u/u)=z u:=by field_simp
  have hl:=complex_log_mul_of_re_pos u (z u/u) hu hq
  rw[he] at hl
  linear_combination -hl
lemma poisson_phase_diagonal_square (S z:ℂ→ℂ) (ν x:ℝ) (K:ℂ) (hν:0<ν) (hx:0<x)
    (hS:AnalyticAt ℂ S (x:ℂ)) (hz:AnalyticAt ℂ z (ν:ℂ))
    (hzv:z (ν:ℂ)=(x:ℂ)) (hs:(x:ℂ)*deriv S (x:ℂ)=(ν:ℂ))
    (hphase:∀ᶠu:ℂ in 𝓝 (ν:ℂ),S (z u)-u-(ν:ℂ)*Complex.log (z u/u)=K):
    (x:ℂ)*(deriv S (x:ℂ)+(x:ℂ)*iteratedDeriv 2 S (x:ℂ))*
      ((ν:ℂ)*deriv z (ν:ℂ)/(x:ℂ))^2=(ν:ℂ):=by
  have hne:(ν:ℂ)≠0:=by exact_mod_cast hν.ne'
  have hxe:(x:ℂ)≠0:=by exact_mod_cast hx.ne'
  have hfc:(fun u:ℂ=>S (z u)-u-(ν:ℂ)*Complex.log (z u)+(ν:ℂ)*Complex.log u)=ᶠ[𝓝 (ν:ℂ)] (fun _:ℂ=>K):=by
    filter_upwards[hphase,log_div_positive_real_germ z ν x hν hx hz hzv] with u hp hl
    rw[hl] at hp
    convert! hp using 1 <;> ring
  have hzero:iteratedDeriv 2 (fun u:ℂ=>S (z u)-u-(ν:ℂ)*Complex.log (z u)+(ν:ℂ)*Complex.log u) (ν:ℂ)=0:=by
    simpa [iteratedDeriv_const] using hfc.iteratedDeriv_eq 2
  have hS':AnalyticAt ℂ S (z (ν:ℂ)):=by rw[hzv];exact hS
  rw[poisson_phase_second_derivative S z (ν:ℂ) (ν:ℂ) hS' hz
    (by rw[hzv];exact Complex.ofReal_mem_slitPlane.mpr hx) (Complex.ofReal_mem_slitPlane.mpr hν),hzv] at hzero
  have hs':deriv S (x:ℂ)=(ν:ℂ)/(x:ℂ):=(eq_div_iff hxe).mpr (by rw[mul_comm];exact hs)
  rw[hs',sub_self,zero_mul,add_zero] at hzero
  rw[hs']
  calc
    _=(ν:ℂ)^2*((iteratedDeriv 2 S (x:ℂ)+(ν:ℂ)*(x:ℂ)⁻¹^2)*(deriv z (ν:ℂ))^2):=by
      field_simp
      ring
    _=(ν:ℂ)^2*((ν:ℂ)*(ν:ℂ)⁻¹^2):=by rw[sub_eq_zero.mp hzero]
    _=(ν:ℂ):=by field_simp
end WP.Analysis
namespace WP.Analysis
open Filter
open scoped Topology
lemma euler_derivative_of_real_germ (S:ℂ→ℂ) (x β:ℝ) (hS:AnalyticAt ℂ S (x:ℂ))
    (hPsi:HasDerivAt WP.Psi β x)
    (hE:(fun t:ℝ=>(t:ℂ)*deriv S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(WP.Psi t:ℂ))):
    deriv S (x:ℂ)+(x:ℂ)*iteratedDeriv 2 S (x:ℂ)=(β:ℂ):=by
  have he:HasDerivAt (fun z:ℂ=>z*deriv S z)
      (deriv S (x:ℂ)+(x:ℂ)*iteratedDeriv 2 S (x:ℂ)) (x:ℂ):=by
    convert! (hasDerivAt_id (x:ℂ)).mul hS.deriv.differentiableAt.hasDerivAt using 1 <;>
      simp only[id_eq,one_mul,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
  have hr:HasDerivAt (fun t:ℝ=>(WP.Psi t:ℂ))
      (deriv S (x:ℂ)+(x:ℂ)*iteratedDeriv 2 S (x:ℂ)) x:=
    he.comp_ofReal.congr_of_eventuallyEq hE.symm
  exact hr.unique hPsi.ofReal_comp
lemma complex_eq_sqrt_of_square (w:ℂ) (t:ℝ) (hRe:0<w.re) (hsq:w^2=(t:ℂ)):
    w=(Real.sqrt t:ℂ):=by
  have hi:=congrArg Complex.im hsq
  simp only[pow_two,Complex.mul_im,Complex.ofReal_im] at hi
  have hwim:w.im=0:=by nlinarith
  have hr:=congrArg Complex.re hsq
  simp only[pow_two,Complex.mul_re,Complex.ofReal_re,hwim,mul_zero,sub_zero] at hr
  apply Complex.ext
  · simp only[Complex.ofReal_re]
    rw[←hr,←pow_two,Real.sqrt_sq_eq_abs,abs_of_pos hRe]
  · simpa only[Complex.ofReal_im] using hwim
end WP.Analysis
namespace WP.Analysis
open Filter
open scoped Topology
lemma poisson_phase_diagonal_jacobian_square (S z:ℂ→ℂ) (ν x:ℝ) (K:ℂ)
    (hν:0<ν) (hx:x∈Set.Ioo (0:ℝ) xCritical)
    (hS:AnalyticAt ℂ S (x:ℂ)) (hz:AnalyticAt ℂ z (ν:ℂ))
    (hzv:z (ν:ℂ)=(x:ℂ)) (hs:(x:ℂ)*deriv S (x:ℂ)=(ν:ℂ))
    (hphase:∀ᶠu:ℂ in 𝓝 (ν:ℂ),S (z u)-u-(ν:ℂ)*Complex.log (z u/u)=K)
    (hE:(fun t:ℝ=>(t:ℂ)*deriv S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(WP.Psi t:ℂ))):
    ((ν:ℂ)*deriv z (ν:ℂ)/(x:ℂ))^2=((ν/(WP.euler WP.Psi x):ℝ):ℂ):=by
  have he:=poisson_phase_diagonal_square S z ν x K hν hx.1 hS hz hzv hs hphase
  have hPsi:HasDerivAt WP.Psi (deriv WP.Psi x) x:=
    (Psi_analyticAt_interior x ⟨hx.1.le,hx.2⟩).differentiableAt.hasDerivAt
  have hED:=euler_derivative_of_real_germ S x (deriv WP.Psi x) hS hPsi hE
  rw[hED,←Complex.ofReal_mul] at he
  have hD:0<WP.euler WP.Psi x:=mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hDn:((WP.euler WP.Psi x:ℝ):ℂ)≠0:=by exact_mod_cast hD.ne'
  rw[Complex.ofReal_div]
  apply (eq_div_iff hDn).mpr
  rw[mul_comm]
  exact he
end WP.Analysis
