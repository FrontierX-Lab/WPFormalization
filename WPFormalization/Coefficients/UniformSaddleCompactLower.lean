import WPFormalization.Coefficients.UniformSaddleCompactCharts
import WPFormalization.Coefficients.UniformSaddleGaussianTransfer
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: CompactLower. -/
noncomputable section
namespace WP.Coefficients
open Set Filter MeasureTheory
open scoped Topology
open WP.Analysis
lemma tiltedKernelMass_compact_central_lower (a:ℝ)(ha:0<a)(har:a≤ r 0):
    ∃T:ℝ,0<T∧∀z∈Icc a (r 0),∀h m:ℕ,0<h→T≤(h:ℝ)→
      (m:ℝ)=(h:ℝ)*unscaledMean z→
      1/(2*Real.sqrt (2*Real.pi))≤
        Real.sqrt ((h:ℝ)*tiltedKernelVariance z)*tiltedKernelMass z h m:=by
  obtain ⟨ρ,hρ,hcharts⟩:=unscaled_kernel_compact_charts a ha har
  obtain ⟨b,hb,hdom⟩:=scaledTiltedKernelFourier_gaussian_domination
  obtain ⟨T,hT,hgauss⟩:=gaussian_central_positive_of_uniform_charts ρ b hρ hb
  refine ⟨T,hT,?_⟩
  intro z hz h m hh hTg hm
  have hz0:0<z:=ha.trans_le hz.1
  obtain ⟨F,hFa,hF0,hF1,hF2,hFb,htrace⟩:=hcharts z hz h hh
  apply hgauss h hTg (scaledTiltedKernelFourier z h) F
    (Real.sqrt ((h:ℝ)*tiltedKernelVariance z)*tiltedKernelMass z h m)
    (scaledTiltedKernelFourier_integrable z hz0 hz.2 h) (hdom z hz0 hz.2 h hh)
    hFa hF0 hF1 hF2 hFb htrace
  exact tiltedKernelMass_scaled_fourier_at_mean z hz0 hz.2 h m hh hm
lemma tiltedKernelMass_compact_polynomial_lower (a:ℝ)(ha:0<a)(har:a≤ r 0):
    ∃c T:ℝ,0<c∧0<T∧∀z∈Icc a (r 0),∀h m:ℕ,0<h→T≤(h:ℝ)→
      (m:ℝ)=(h:ℝ)*unscaledMean z→c/((m:ℝ)+1)≤ tiltedKernelMass z h m:=by
  obtain ⟨T,hT,hcentral⟩:=tiltedKernelMass_compact_central_lower a ha har
  obtain ⟨C,hC,hmean⟩:=unscaledMean_uniform_linear_variance_bounds
  let D:ℝ:=Real.sqrt (5*C)
  have hD:0<D:=Real.sqrt_pos.mpr (by positivity)
  let κ:ℝ:=1/(2*Real.sqrt (2*Real.pi))
  have hκ:0<κ:=by dsimp[κ];positivity
  refine ⟨κ/D,T,div_pos hκ hD,hT,?_⟩
  intro z hz h m hh hTg hm
  have hz0:0<z:=ha.trans_le hz.1
  have hzfull:z∈Icc (0:ℝ) (r 0):=⟨hz0.le,hz.2⟩
  have hhR:0<(h:ℝ):=by exact_mod_cast hh
  have hv:0<tiltedKernelVariance z:=tiltedKernelVariance_pos z hz0 hz.2
  let σ:ℝ:=Real.sqrt ((h:ℝ)*tiltedKernelVariance z)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hhR hv)
  have hσsq:σ^2=(h:ℝ)*z*deriv unscaledMean z:=by
    rw[Real.sq_sqrt (mul_pos hhR hv).le]
    dsimp[tiltedKernelVariance]
    ring
  have hpm:0<tiltedKernelMass z h m:=tiltedKernelMass_pos z hz0 hz.2 h m hh
  have hlo:κ≤σ*tiltedKernelMass z h m:=hcentral z hz h m hh hTg hm
  have hhzm:(h:ℝ)*z≤5*(m:ℝ):=by
    have hu:=(hmean z hzfull).1
    have he:=mul_le_mul_of_nonneg_left hu hhR.le
    rw[←hm] at he
    nlinarith
  have hsquare:σ^2≤5*C*(m:ℝ):=by
    have ht:=mul_le_mul_of_nonneg_left (hmean z hzfull).2.2.2 (mul_pos hhR hz0).le
    rw[←hσsq] at ht
    have hu:=mul_le_mul_of_nonneg_right hhzm hC.le
    nlinarith
  have hσD:σ≤ D*((m:ℝ)+1):=by
    have hDsq:D^2=5*C:=Real.sq_sqrt (by positivity)
    have hmR:0≤(m:ℝ):=Nat.cast_nonneg m
    apply (sq_le_sq₀ hσ.le (by positivity)).mp
    rw[mul_pow,hDsq]
    have hmquad:(m:ℝ)≤((m:ℝ)+1)^2:=by nlinarith[sq_nonneg (m:ℝ)]
    exact hsquare.trans (mul_le_mul_of_nonneg_left hmquad (by positivity))
  apply (div_le_iff₀ (by positivity:(0:ℝ)<(m:ℝ)+1)).mpr
  apply (div_le_iff₀ hD).mpr
  have ht:=mul_le_mul_of_nonneg_right hσD hpm.le
  nlinarith
end WP.Coefficients
