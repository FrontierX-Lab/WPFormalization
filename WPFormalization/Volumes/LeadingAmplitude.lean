import WPFormalization.Volumes.OriginNormalization
import WPFormalization.Analysis.BesselSignBounds
import WPFormalization.Analysis.ParameterDerivatives
/-! The original integral varpi is exactly the first marked amplitude.
The identity uses the actual X differential equation and stationary kernel,
including the removable X(v)/v value at zero. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
lemma Xdiv_eq_neg_second (v:ℝ):
    Xdiv v=-(iteratedDeriv 2 X (v:ℂ)).re:=by
  by_cases hv:v=0
  · subst v
    simp only[Xdiv,ite_true,Complex.ofReal_zero]
    have he:=iteratedDeriv_X_succ_zero 1
    norm_num at he
    rw[he]
    norm_num
  · rw[Xdiv,ite_eq_right hv,XR_eq_neg_mul_second]
    field_simp

lemma varpi_integral_kernel (Y:ℝ)(hY:Y∈Ico 0 y₀):
    (∫s:ℝ in (0)..1,(1-s^2)*Xdiv (T Y-Delta Y*s^2))=
      -2*(deriv (K Y) (r Y)).re:=by
  have he:(∫s:ℝ in (0)..1,(1-s^2)*Xdiv (T Y-Delta Y*s^2))=
      -stationaryWeighted (fun s=>1-s^2) (deriv (deriv X)) Y (T Y):=by
    rw[stationaryWeighted_real_integral _ (by fun_prop) _
      X_differentiable.deriv.deriv.continuous,←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw[Xdiv_eq_neg_second]
    simp only[Delta,iteratedDeriv_succ,iteratedDeriv_zero,iteratedDeriv_one]
    ring
  rw[he,stationary_second_moment_T]
  have hr:2*(T Y-Y)=r Y:=by have hh:=T_eq_firstKernelEndpoint Y hY;linarith
  rw[hr]
  ring
lemma marked_amplitude_one_eq_varpi (Y:ℝ)(hY:Y∈Ico 0 y₀):
    Real.rpow (r Y) (1/2:ℝ)*Real.sqrt (A Y*Theta Y)=varpi Y:=by
  have hD:0<Delta Y:=Delta_pos Y hY
  have hr:0<r Y:=r_pos Y hY
  have ha:0<a Y:=a_pos Y hY
  have hK: (deriv (K Y) (r Y)).re<0:=K_deriv_at_r_re_neg Y hY
  have hpowD:0<Real.rpow (Delta Y) (3/2:ℝ):=Real.rpow_pos_of_pos hD _
  have htwo:Real.rpow 2 (3/2:ℝ)=2*Real.sqrt 2:=by
    rw[Real.rpow_eq_pow,show (3/2:ℝ)=1+1/2 by ring,Real.rpow_add (by norm_num),Real.rpow_one,←Real.sqrt_eq_rpow]
  have hpowr:Real.rpow (r Y) (3/2:ℝ)=2*Real.sqrt 2*Real.rpow (Delta Y) (3/2:ℝ):=by
    simp only[Real.rpow_eq_pow] at htwo ⊢
    rw[(stationary_root_proof Y hY).2.2.2,Real.mul_rpow (by norm_num) hD.le,htwo]
  have hZ:A Y*a Y*Real.rpow (r Y) (3/2:ℝ)=Real.sqrt 2*action Y:=
    (kernel_action_moments Y hY).2.2
  rw[hpowr] at hZ
  have hZ':2*A Y*a Y*Real.rpow (Delta Y) (3/2:ℝ)=action Y:=by
    apply mul_left_cancel₀ (show Real.sqrt 2≠0 by positivity)
    convert hZ using 1;ring
  have hscale:(deriv (barK Y) 1).re=r Y*(deriv (K Y) (r Y)).re/a Y:=by
    rw[barK_deriv_interior Y hY 1,mul_one,div_eq_mul_inv,←Complex.ofReal_inv]
    simp only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero]
    ring
  have hTheta:= (kernel_action_moments Y hY).1
  rw[hscale] at hTheta
  have hrad:action Y/Real.rpow (Delta Y) (3/2:ℝ)/
      (∫s:ℝ in (0)..1,(1-s^2)*Xdiv (T Y-Delta Y*s^2))=r Y*(A Y*Theta Y):=by
    rw[varpi_integral_kernel Y hY,hTheta]
    field_simp[hpowD.ne',hr.ne',ha.ne',hK.ne]
    nlinarith[hZ']
  rw[varpi,hrad,Real.sqrt_mul hr.le]
  simp only[Real.rpow_eq_pow,Real.sqrt_eq_rpow]

end WP.Analysis
