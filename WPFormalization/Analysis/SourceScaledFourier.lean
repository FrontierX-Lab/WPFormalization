import WPFormalization.Analysis.SignedCoefficientFourier
import WPFormalization.Analysis.OriginStandardGaussian
/-! Exact normalized-source circle coefficients from the already proved
integer Fourier inversion. Radius and centering hypotheses are explicit. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory

def sourceCirclePGF (F:ℂ→ℂ)(x:ℝ)(w:ℂ):ℂ:=F ((x:ℂ)*w)/F (x:ℂ)
lemma sourceCirclePGF_analytic (F:ℂ→ℂ)(x R:ℝ)(hx:0<x)
    (hF:AnalyticOnNhd ℂ F (Metric.ball 0 R)):
    AnalyticOnNhd ℂ (sourceCirclePGF F x) (Metric.ball 0 (R/x)):=by
  intro w hw
  have hn:‖w‖<R/x:=by simpa only[Metric.mem_ball,dist_zero_right] using hw
  have hz:‖(x:ℂ)*w‖<R:=by
    rw[norm_mul,Complex.norm_of_nonneg hx.le,mul_comm]
    exact (lt_div_iff₀ hx).mp hn
  exact ((hF _ (by simpa only[Metric.mem_ball,dist_zero_right] using hz)).comp
    (by fun_prop:AnalyticAt ℂ (fun w:ℂ=>(x:ℂ)*w) w)).div_const
lemma sourceCirclePGF_coeff (F:ℂ→ℂ)(x:ℝ)(k:ℕ):
    WP.coeff (sourceCirclePGF F x) k=(x:ℂ)^k*WP.coeff F k/F (x:ℂ):=by
  unfold sourceCirclePGF WP.coeff
  rw[iteratedDeriv_div_const,iteratedDeriv_comp_mul_left,mul_zero]
  ring
lemma source_coefficient_scaled_fourier (F:ℂ→ℂ)(x R σ:ℝ)(k:ℕ)(Q:ℂ)
    (hx:0<x)(hxR:x<R)(hσ:0<σ)(hQ:Q≠0)(hFx:F (x:ℂ)≠0)
    (hF:AnalyticOnNhd ℂ F (Metric.ball 0 R)):
    WP.coeff F k/Q=F (x:ℂ)/((x:ℂ)^k*(σ:ℂ)*Q)*((2*Real.pi:ℝ):ℂ)⁻¹*
      ∫t:ℝ,scaledCenteredFourier (sourceCirclePGF F x) (k:ℝ) σ t:=by
  have hRx:1<R/x:=(one_lt_div hx).mpr hxR
  have hfa:=sourceCirclePGF_analytic F x R hx hF
  have he:=signedTaylorCoeff_scaled_fourier (sourceCirclePGF F x) (R/x) hRx hfa.differentiableOn
    (k:ℝ) σ hσ (k:ℤ)
  simp only[signedTaylorCoeff,Int.natCast_nonneg,ite_true,Int.toNat_natCast,Int.cast_natCast,
    sub_self,zero_div,Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,one_mul] at he
  have hx0:(x:ℂ)≠0:=by exact_mod_cast hx.ne'
  have hσ0:(σ:ℂ)≠0:=by exact_mod_cast hσ.ne'
  calc _=(F (x:ℂ)/((x:ℂ)^k*(σ:ℂ)*Q))*((σ:ℂ)*WP.coeff (sourceCirclePGF F x) k):=by
            rw[sourceCirclePGF_coeff]
            field_simp
            <;>ring
       _= _:=by rw[he];ring
lemma sourceCirclePGF_sphere_continuous (F:ℂ→ℂ)(x R:ℝ)(hx:0<x)(hxR:x<R)
    (hF:AnalyticOnNhd ℂ F (Metric.ball 0 R)):
    ContinuousOn (sourceCirclePGF F x) (Metric.sphere 0 1):=by
  apply (sourceCirclePGF_analytic F x R hx hF).continuousOn.mono
  intro z hz
  have hn:‖z‖=1:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
  simpa only[Metric.mem_ball,dist_zero_right,hn] using (one_lt_div hx).mpr hxR
end WP.Analysis
