import WPFormalization.Volumes.PoissonLeadingDiagonal
import WPFormalization.HigherOrder.OriginPoissonFamily
import WPFormalization.HigherOrder.PoissonFamilyCoefficientBounds
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma originPoissonFamily_leading_diagonal_germ (P:PsiTheory) (p:ℕ) (Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ)
    (S xco Q:ℂ→ℂ) (Z:ℂ × ℂ → ℂ) (R ρ:ℝ) (hR:0<R) (hρ:0<ρ)
    (hS:AnalyticAt ℂ S 0) (hSd:deriv S 0≠0)
    (hxco:AnalyticAt ℂ xco 0) (hxco0:xco 0=0)
    (hZ:AnalyticOnNhd ℂ Z (Metric.ball 0 R ×ˢ Metric.ball 0 R))
    (haxes:∀ν:ℂ,‖ν‖<R→xco ν*deriv S (xco ν)=ν∧Z (0,ν)=0∧Z (ν,ν)=xco ν)
    (hphase:∀u ν:ℂ,‖u‖<R→‖ν‖<R→phaseQuotient Z u ν≠0∧
      S (Z (u,ν))-u-ν*Complex.log (phaseQuotient Z u ν)=S (xco ν)-ν+ν*Complex.log (Q ν))
    (hEuler:∀ᶠx:ℝ in 𝓝 0,0≤x→(x:ℂ)*deriv S (x:ℂ)=(WP.Psi x:ℂ))
    (hampR:∀j t,t∈Icc (0:ℝ) ρ → originMarkedAmplitude P p j Bc L (t:ℂ)=
      ((extractionB p t*markedCoefficient P p j (inverseY t):ℝ):ℂ)):
    ∀ᶠν:ℝ in 𝓝[≥] (0:ℝ),0<ν→
      poissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) 0 (ν:ℂ)=
        ((extractionB p (XR (densityY (2*ν)))*
          Real.sqrt (ν/WP.euler WP.Psi (XR (densityY (2*ν)))):ℝ):ℂ):=by
  have hsaddle:∀ᶠν:ℂ in 𝓝 0,xco ν*deriv S (xco ν)=ν:=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) hR] with ν hν
    exact (haxes ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)).1
  have hm:=Analysis.origin_saddle_matches_densityY S xco hS hSd hxco hxco0 hsaddle hEuler
  have hj:=Analysis.poisson_phase_leading_diagonal_germ S xco Q Z R hR hS hSd hxco hxco0 hZ haxes hphase hEuler
  filter_upwards[hm,hj,Analysis.densitySaddle_tendsto_zero_right.eventually (eventually_lt_nhds hρ),
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with ν hm hj hxρ hνR hν
  let x:ℝ:=XR (densityY (2*ν))
  have hx:x∈Ioo (0:ℝ) xCritical:=(Analysis.physicalDensitySaddle_spec ν hν).1
  have hn:‖(ν:ℂ)‖<R:=by simpa only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos hν] using hνR
  have hzv:Z ((ν:ℂ),(ν:ℂ))=(x:ℂ):=(haxes (ν:ℂ) hn).2.2.trans hm
  rw[poissonFamilyCoefficient_zero,originPoissonAmplitude,Analysis.phaseAmplitude_eq_mul_unit,hzv,
    hampR 0 x ⟨hx.1.le,hxρ.le⟩,hj hν]
  simp only[markedCoefficient_zero,mul_one,Complex.ofReal_mul,x]
end WP.HigherOrder
