import WPFormalization.Analysis.HarmonicFourierScaling
import WPFormalization.Analysis.OriginStandardGaussian
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
open scoped Interval
lemma circle_integral_outer_localization (f:ℝ→ℂ)(hf:ContinuousOn f (Icc (-Real.pi) Real.pi))(δ B:ℝ)
    (hδ:0<δ)(hδπ:δ≤Real.pi)(hB:0≤B)
    (hbound:∀θ:ℝ,δ≤|θ|→|θ|≤Real.pi→‖f θ‖≤B):
    ‖(∫θ:ℝ in (-Real.pi)..Real.pi,f θ)-(∫θ:ℝ in (-δ)..δ,f θ)‖≤2*Real.pi*B:=by
  have hleft:‖∫θ:ℝ in (-Real.pi)..(-δ),f θ‖≤B*(Real.pi-δ):=by
    have ht:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=-Real.pi) (b:=-δ) (C:=B) (fun θ hθ=>by
      rw[uIoc_of_le (by linarith:-Real.pi≤-δ)] at hθ
      apply hbound θ
      · rw[abs_of_nonpos (by linarith[hθ.2]:θ≤0)]
        linarith[hθ.2]
      · rw[abs_of_nonpos (by linarith[hθ.2]:θ≤0)]
        linarith[hθ.1])
    simpa only[neg_sub_neg,abs_of_nonneg (sub_nonneg.mpr hδπ)] using ht
  have hright:‖∫θ:ℝ in δ..Real.pi,f θ‖≤B*(Real.pi-δ):=by
    have ht:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=δ) (b:=Real.pi) (C:=B) (fun θ hθ=>by
      rw[uIoc_of_le hδπ] at hθ
      apply hbound θ
      · rw[abs_of_nonneg (by linarith[hθ.1]:0≤θ)]
        exact hθ.1.le
      · rw[abs_of_nonneg (by linarith[hθ.1]:0≤θ)]
        exact hθ.2)
    simpa only[abs_of_nonneg (sub_nonneg.mpr hδπ)] using ht
  have hsplit:(∫θ:ℝ in (-Real.pi)..Real.pi,f θ)-(∫θ:ℝ in (-δ)..δ,f θ)=
      (∫θ:ℝ in (-Real.pi)..(-δ),f θ)+(∫θ:ℝ in δ..Real.pi,f θ):=by
    have hi (a b:ℝ)(ha:-Real.pi≤a)(hab:a≤b)(hb:b≤Real.pi):
        IntervalIntegrable f volume a b:=
      (hf.mono (by intro x hx;exact ⟨ha.trans hx.1,hx.2.trans hb⟩)).intervalIntegrable_of_Icc hab
    have h1:=intervalIntegral.integral_add_adjacent_intervals
      (hi (-Real.pi) (-δ) le_rfl (by linarith) (by linarith[Real.pi_pos]))
      (hi (-δ) Real.pi (by linarith) (by linarith[Real.pi_pos]) le_rfl)
    have h2:=intervalIntegral.integral_add_adjacent_intervals
      (hi (-δ) δ (by linarith) (by linarith) (by linarith))
      (hi δ Real.pi (by linarith[Real.pi_pos]) hδπ le_rfl)
    rw[←h1,←h2]
    abel
  rw[hsplit]
  apply (norm_add_le _ _).trans
  have ht:=add_le_add hleft hright
  nlinarith[mul_nonneg hδ.le hB]
end WP.Analysis

namespace WP.Analysis
open Set MeasureTheory
lemma coefficient_centered_circle_identity (F:ℂ→ℂ)(x:ℝ)(a:ℂ)(k:ℕ)(hx:0<x)
    (hF:AnalyticOnNhd ℂ F (Metric.closedBall 0 x)):
    a*(x:ℂ)^k*WP.coeff F k=((2*Real.pi:ℝ):ℂ)⁻¹*
      ∫θ:ℝ in (-Real.pi)..Real.pi,
        Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*a*
          F ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)):=by
  have hmap:MapsTo (fun z:ℂ=>(x:ℂ)*z) (Metric.closedBall 0 1) (Metric.closedBall 0 x):=by
    intro z hz
    rw[Metric.mem_closedBall,dist_zero_right] at hz ⊢
    rw[norm_mul,Complex.norm_of_nonneg hx.le]
    nlinarith[norm_nonneg z]
  have hg:DifferentiableOn ℂ (fun z:ℂ=>F ((x:ℂ)*z)) (Metric.closedBall 0 1):=by
    intro z hz
    exact ((hF _ (hmap hz)).differentiableAt.comp z (by fun_prop)).differentiableWithinAt
  have he:=coeff_eq_symmetric_fourier_integral (fun z:ℂ=>F ((x:ℂ)*z)) hg k
  rw[coeff_complex_scale_left F (x:ℂ) k] at he
  rw[mul_assoc,he]
  rw[←mul_assoc,mul_comm a _,mul_assoc,←intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  ring
lemma centered_circle_coefficient_local_error (F:ℂ→ℂ)(x:ℝ)(a:ℂ)(k:ℕ)(δ B:ℝ)
    (hx:0<x)(hF:AnalyticOnNhd ℂ F (Metric.closedBall 0 x))
    (hδ:0<δ)(hδπ:δ≤Real.pi)(hB:0≤B)
    (hbound:∀θ:ℝ,δ≤|θ|→|θ|≤Real.pi→
      ‖Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*a*F ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤B):
    ‖a*(x:ℂ)^k*WP.coeff F k-((2*Real.pi:ℝ):ℂ)⁻¹*
      ∫θ:ℝ in (-δ)..δ,Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*a*
        F ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤B:=by
  have hmap:MapsTo (fun θ:ℝ=>(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
      (Icc (-Real.pi) Real.pi) (Metric.closedBall 0 x):=by
    intro θ hθ
    rw[Metric.mem_closedBall,dist_zero_right,norm_mul,Complex.norm_of_nonneg hx.le,
      Complex.norm_exp_ofReal_mul_I,mul_one]
  have hc:ContinuousOn (fun θ:ℝ=>Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*a*
      F ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))) (Icc (-Real.pi) Real.pi):=by
    apply ContinuousOn.mul (by fun_prop)
    exact hF.continuousOn.comp (by fun_prop) hmap
  rw[coefficient_centered_circle_identity F x a k hx hF,←mul_sub,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity:0<2*Real.pi)]
  have ht:=circle_integral_outer_localization _ hc δ B hδ hδπ hB hbound
  apply (mul_le_mul_of_nonneg_left ht (by positivity:(0:ℝ)≤(2*Real.pi)⁻¹)).trans_eq
  field_simp
end WP.Analysis

namespace WP.Analysis
lemma gaussian_normalized_circle_local_error (F:ℂ→ℂ)(x h v:ℝ)(a Bc raw:ℂ)(k:ℕ)(δ B:ℝ)
    (hx:0<x)(hh:0<h)(hv:0<v)(hBc:Bc≠0)
    (hF:AnalyticOnNhd ℂ F (Metric.closedBall 0 x))
    (hδ:0<δ)(hδπ:δ≤Real.pi)(hB:0≤B)
    (hbound:∀θ:ℝ,δ≤|θ|→|θ|≤Real.pi→
      ‖Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*a*F ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤B)
    (hraw:raw=(Real.sqrt h:ℂ)*(Real.sqrt v:ℂ)/Bc*
      ∫θ:ℝ in (-δ)..δ,Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*a*
        F ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))):
    ‖a*(x:ℂ)^k*WP.coeff F k*(Real.sqrt (2*Real.pi*h*v):ℂ)/Bc-
      raw/(Real.sqrt (2*Real.pi):ℂ)‖≤Real.sqrt (2*Real.pi)*Real.sqrt v/‖Bc‖*Real.sqrt h*B:=by
  have hq:0<Real.sqrt (2*Real.pi):=by positivity
  have hq0:(Real.sqrt (2*Real.pi):ℂ)≠0:=by exact_mod_cast hq.ne'
  have hs:Real.sqrt (2*Real.pi*h*v)=Real.sqrt (2*Real.pi)*Real.sqrt h*Real.sqrt v:=by
    rw[Real.sqrt_mul (by positivity:0≤2*Real.pi*h),Real.sqrt_mul (by positivity:0≤2*Real.pi)]
  have hs2:(Real.sqrt (2*Real.pi):ℂ)^2=(2*Real.pi:ℝ):=by exact_mod_cast Real.sq_sqrt (by positivity:0≤2*Real.pi)
  have hid:a*(x:ℂ)^k*WP.coeff F k*(Real.sqrt (2*Real.pi*h*v):ℂ)/Bc-
      raw/(Real.sqrt (2*Real.pi):ℂ)=
      ((Real.sqrt (2*Real.pi*h*v):ℂ)/Bc)*
        (a*(x:ℂ)^k*WP.coeff F k-((2*Real.pi:ℝ):ℂ)⁻¹*
          ∫θ:ℝ in (-δ)..δ,Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*a*
            F ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))):=by
    generalize hI:(∫θ:ℝ in (-δ)..δ,Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*a*
      F ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))=J at hraw ⊢
    rw[hraw,hs,Complex.ofReal_mul,Complex.ofReal_mul,←hs2]
    field_simp
    <;>ring
  rw[hid,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have he:=centered_circle_coefficient_local_error F x a k δ B hx hF hδ hδπ hB hbound
  apply (mul_le_mul_of_nonneg_left he (by positivity:0≤Real.sqrt (2*Real.pi*h*v)/‖Bc‖)).trans_eq
  rw[hs]
  ring
end WP.Analysis
