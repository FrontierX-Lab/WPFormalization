import Mathlib
/-! Negative lattice Fourier modes of an actual analytic disk function vanish.
The proof uses a native holomorphic primitive and the genuine circle map. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory Complex
lemma analytic_circle_negative_fourier (f:ℂ→ℂ)(R:ℝ)(hR:1<R)
    (hf:DifferentiableOn ℂ f (Metric.ball 0 R))(m:ℕ):
    (∫θ:ℝ in (-Real.pi)..Real.pi,
      Complex.exp ((θ:ℂ)*Complex.I)^(m+1)*f (Complex.exp ((θ:ℂ)*Complex.I)))=0:=by
  let g:ℂ→ℂ:=fun z=>z^m*f z
  have hg:DifferentiableOn ℂ g (Metric.ball 0 R):=by
    intro z hz
    have hfa:DifferentiableAt ℂ f z:=(hf z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    exact ((differentiableAt_id.pow m).mul hfa).differentiableWithinAt
  obtain ⟨F,hF⟩:=hg.isExactOn_ball
  have hzero:(∮z in C((0:ℂ),1),g z)=0:=by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt (by norm_num)
    intro z hz
    apply (hF z ?_).hasDerivWithinAt
    have hn:‖z‖=1:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
    simpa only[Metric.mem_ball,dist_zero_right,hn] using hR
  let H:ℝ→ℂ:=fun θ=>circleMap 0 1 θ^(m+1)*f (circleMap 0 1 θ)
  have hcircle:(∮z in C((0:ℂ),1),g z)=Complex.I*(∫θ:ℝ in (0)..(2*Real.pi),H θ):=by
    rw[circleIntegral,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp only[g,H]
    rw[deriv_circleMap,smul_eq_mul]
    rw[pow_succ]
    ring
  have h02:(∫θ:ℝ in (0)..(2*Real.pi),H θ)=0:=
    (mul_eq_zero.mp (hcircle.symm.trans hzero)).resolve_left Complex.I_ne_zero
  have hp:Function.Periodic H (2*Real.pi):=(periodic_circleMap 0 1).comp (fun z=>z^(m+1)*f z)
  have hshift:=hp.intervalIntegral_add_eq 0 (-Real.pi)
  rw[zero_add,show -Real.pi+2*Real.pi=Real.pi by ring] at hshift
  rw[hshift] at h02
  simpa only[H,circleMap,Complex.ofReal_one,one_mul,zero_add] using h02
end WP.Analysis
