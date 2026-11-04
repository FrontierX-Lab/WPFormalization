import WPFormalization.Analysis.KernelWeightMoments
import WPFormalization.Analysis.ParameterDerivatives
import WPFormalization.Analysis.DeflatedKernel
/-! Exact first parameter identities for the actual first-root kernel.
The total canonical weight is written as its defining sum, so this analysis
module stays independent of Marked; its sum is definitionally WP.Theta.
The stationary equation gives Theta = -2 T′, including Y=0. The derivative
of the original first root r is proved on the open physical interval only;
no unproved extension of the endpoint r definition is used. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma Theta_eq_neg_two_T_deriv (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    (∑' l : ℕ, weight Y l) = -2*deriv T Y := by
  have hdom := stationaryParameterDomain_contains Y hY
  have hroot := (T_root_on_stationaryParameterDomain Y hdom).2
  have hstation := T_deriv_stationary_equation_on_domain Y hdom
  have hmoment := stationary_second_moment_identity Y (T Y)
  have hdiff := stationary_second_moment_T Y (T Y)
  have hr : 2*(T Y-Y)=r Y := by have ht:=T_eq_firstKernelEndpoint Y hY;linarith
  rw [hroot,hr] at hmoment
  rw [hr] at hdiff
  rw [hdiff] at hstation
  have ha := a_pos Y hY
  have hrpos := r_pos Y hY
  have hk := K_deriv_at_r_re_neg Y hY
  have hmul := congrArg (fun t : ℝ => r Y*t) hstation
  have he : a Y=2*r Y*deriv T Y*(deriv (K Y) (r Y)).re := by nlinarith
  have hscale : (deriv (barK Y) 1).re = r Y*(deriv (K Y) (r Y)).re/a Y := by
    rw [barK_deriv_interior Y hY 1,mul_one,div_eq_mul_inv,←Complex.ofReal_inv]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero]
    ring
  rw [theta_sum_kernel_deriv Y ⟨hY.1,hY.2.le⟩,hscale]
  field_simp [ha.ne',hrpos.ne',hk.ne]
  nlinarith
end WP.Analysis
namespace WP.Analysis
lemma r_hasDerivAt_open_parameter (Y : ℝ) (hY : Y ∈ Ioo 0 y₀) :
    HasDerivAt r (-((∑' l : ℕ, weight Y l)+2)) Y := by
  have hYi : Y ∈ Ico 0 y₀ := ⟨hY.1.le,hY.2⟩
  have hd := (((T_analyticAt_interior Y hYi).differentiableAt.hasDerivAt).sub
    (hasDerivAt_id Y)).const_mul 2
  have he : r =ᶠ[𝓝 Y] (fun x : ℝ => 2*(T x-x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with x hx
    have ht := T_eq_firstKernelEndpoint x ⟨hx.1.le,hx.2⟩
    linarith
  have hd' := hd.congr_of_eventuallyEq he
  convert hd' using 1
  rw [Theta_eq_neg_two_T_deriv Y hYi]
  ring
end WP.Analysis
