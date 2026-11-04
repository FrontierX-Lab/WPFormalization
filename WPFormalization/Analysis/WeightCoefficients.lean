import WPFormalization.Analysis.DeflatedKernel
import WPFormalization.Analysis.HarmonicMass

/-! The true generating germ of the canonical increments theta_n-theta_(n-1).
The removable first-root quotient identifies its Taylor coefficients exactly
with the original weight definition, including the critical endpoint. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex PowerSeries
open scoped Topology

def weightGenerating (Y:ℝ) (w:ℂ):ℂ := (deflatedBarK Y w)⁻¹
lemma deflatedBarK_zero (Y:ℝ) (hY:Y∈Icc 0 y₀):deflatedBarK Y 0=1 := by
  have h:=deflatedBarK_identity Y hY 0
  simpa only [sub_zero,one_mul,barK_zero_closed Y hY] using h
lemma weightGenerating_zero (Y:ℝ) (hY:Y∈Icc 0 y₀):weightGenerating Y 0=1 := by
  simp only [weightGenerating,deflatedBarK_zero Y hY,inv_one]
lemma weightGenerating_germ (Y:ℝ) (hY:Y∈Icc 0 y₀):
    weightGenerating Y =ᶠ[𝓝 (0:ℂ)] (fun z:ℂ=>(1-z)*(barK Y z)⁻¹) := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1)] with z hz
  have hn:‖z‖<1:=by simpa only [Metric.mem_ball,dist_zero_right] using hz
  have hw:1-z≠0:=by
    intro he
    have he':z=1:=(sub_eq_zero.mp he).symm
    rw [he',norm_one] at hn
    exact lt_irrefl _ hn
  unfold weightGenerating
  calc
    _ = ((1-z)*(1-z)⁻¹)*(deflatedBarK Y z)⁻¹ := by rw [mul_inv_cancel₀ hw,one_mul]
    _ = (1-z)*((1-z)*deflatedBarK Y z)⁻¹ := by rw [mul_inv_rev];ring
    _ = _ := by rw [deflatedBarK_identity Y hY]
lemma weightGenerating_taylor (Y:ℝ) (hY:Y∈Icc 0 y₀):
    taylor (weightGenerating Y)=(PowerSeries.C 1-PowerSeries.X)*taylor (fun z=>(barK Y z)⁻¹) := by
  have hf:AnalyticAt ℂ (fun z:ℂ=>1-z) 0 := by fun_prop
  have hg:AnalyticAt ℂ (fun z:ℂ=>(barK Y z)⁻¹) 0 :=
    ((barK_differentiable Y).analyticAt 0).inv (by rw [barK_zero_closed Y hY];norm_num)
  rw [taylor_congr (weightGenerating_germ Y hY),taylor_mul hf hg]
  have hl:=taylor_sub (f:=fun _:ℂ=>(1:ℂ)) (g:=fun z:ℂ=>z) analyticAt_const analyticAt_id
  simp only [taylor_const,taylor_id] at hl
  rw [hl]

lemma weightGenerating_coeff (Y:ℝ) (hY:Y∈Icc 0 y₀) (n:ℕ):
    realCoeff (weightGenerating Y) n=weight Y n := by
  have h:=congrArg (fun p:PowerSeries ℂ=>(PowerSeries.coeff n p).re) (weightGenerating_taylor Y hY)
  rw [sub_mul] at h
  simp only [taylor_coeff,map_sub,PowerSeries.coeff_C_mul,one_mul,Complex.sub_re] at h
  cases n with
  | zero => simpa [realCoeff,weight,theta] using h
  | succ n => simpa [realCoeff,weight,theta] using h
end WP.Analysis
