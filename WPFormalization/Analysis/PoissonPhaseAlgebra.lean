import Mathlib
noncomputable section
namespace WP.Analysis
lemma complex_log_mul_of_re_pos (a b:ℂ) (ha:0<a.re) (hb:0<b.re):
    Complex.log (a*b)=Complex.log a+Complex.log b:=by
  have han:a≠0:=by intro h;rw[h,Complex.zero_re] at ha;exact(lt_irrefl _ ha)
  have hbn:b≠0:=by intro h;rw[h,Complex.zero_re] at hb;exact(lt_irrefl _ hb)
  have haa:|a.arg|<Real.pi/2:=Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have hba:|b.arg|<Real.pi/2:=Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hh:|a.arg+b.arg|<Real.pi:=(abs_add_le _ _).trans_lt (by linarith)
  exact (Complex.log_mul_eq_add_log_iff han hbn).mpr ⟨(abs_lt.mp hh).1,(abs_lt.mp hh).2.le⟩
lemma complex_log_inv_of_re_pos (a:ℂ) (ha:0<a.re):Complex.log a⁻¹= -Complex.log a:=
  Complex.log_inv a (Complex.slitPlane_arg_ne_pi (Or.inl ha))
lemma poisson_eta_phase_algebra (s sx z x c ν D η L:ℂ) (hc:c≠0)
    (hsaddle:x*c=ν)
    (hD:s-sx-(z-x)*c=(z-x)^2*D)
    (hη:D-η+ν*(η/c)^2*L=0)
    (hL:Complex.log (1+(z-x)*η/c)-(z-x)*η/c=((z-x)*η/c)^2*L):
    s-z*(c+(z-x)*η)+ν*(Complex.log c+Complex.log (1+(z-x)*η/c))=
      sx-ν+ν*Complex.log c:=by
  have he:(z-x)^2*D-(z-x)^2*η+ν*((z-x)*η/c)^2*L=0:=by
    linear_combination (z-x)^2*hη
  have hcore:s-(z-x)*c-(z-x)^2*η+ν*Complex.log (1+(z-x)*η/c)=sx+ν*((z-x)*η/c):=by
    linear_combination hD+he+ν*hL
  have hνt:ν*((z-x)*η/c)=x*(z-x)*η:=by
    rw[←hsaddle]
    field_simp[hc]
    <;>ring
  have hu:z*(c+(z-x)*η)=(z-x)*c+ν+(z-x)^2*η+ν*((z-x)*η/c):=by
    rw[hνt,←hsaddle]
    ring
  rw[hu]
  linear_combination hcore
lemma poisson_eta_phase_log_identity (s sx z x c ν D η L:ℂ) (hc:0<c.re)
    (hsaddle:x*c=ν)
    (hD:s-sx-(z-x)*c=(z-x)^2*D)
    (hη:D-η+ν*(η/c)^2*L=0)
    (hL:Complex.log (1+(z-x)*η/c)-(z-x)*η/c=((z-x)*η/c)^2*L)
    (ht:0<(1+(z-x)*η/c).re) (hu:0<(c+(z-x)*η).re):
    s-z*(c+(z-x)*η)-ν*Complex.log ((c+(z-x)*η)⁻¹)=
      sx-ν+ν*Complex.log c:=by
  have hcn:c≠0:=by intro h;rw[h,Complex.zero_re] at hc;exact(lt_irrefl _ hc)
  have hprod:c+(z-x)*η=c*(1+(z-x)*η/c):=by field_simp[hcn] <;>ring
  have hlog:Complex.log ((c+(z-x)*η)⁻¹)= -(Complex.log c+Complex.log (1+(z-x)*η/c)):=by
    rw[complex_log_inv_of_re_pos _ hu,hprod,complex_log_mul_of_re_pos _ _ hc ht]
  rw[hlog]
  have hh:=poisson_eta_phase_algebra s sx z x c ν D η L hcn hsaddle hD hη hL
  linear_combination hh
end WP.Analysis
