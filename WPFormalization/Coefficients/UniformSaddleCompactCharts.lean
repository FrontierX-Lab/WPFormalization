import WPFormalization.Coefficients.UniformSaddleCompactPhase
import WPFormalization.Coefficients.UniformSaddleFourier
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: CompactCharts. -/
noncomputable section
namespace WP.Coefficients
open Set Filter MeasureTheory
open scoped Topology
open WP.Analysis
lemma centeredKernelSlice_exp (S:ℂ→ℂ)(h:ℕ)(z c u:ℂ)
    (hEz:Complex.exp (S z)=(H 0 z)⁻¹)
    (hEu:Complex.exp (S (z*Complex.exp (c*u)))=(H 0 (z*Complex.exp (c*u)))⁻¹):
    Complex.exp ((h:ℂ)*centeredExponentialSlice S z c u)=
      Complex.exp (-((h:ℂ)*c*u*complexEuler S z))*(H 0 z/H 0 (z*Complex.exp (c*u)))^h:=by
  have he:(h:ℂ)*centeredExponentialSlice S z c u=
      -((h:ℂ)*c*u*complexEuler S z)+(h:ℂ)*(S (z*Complex.exp (c*u))-S z):=by
    dsimp[centeredExponentialSlice]
    ring
  rw[he,Complex.exp_add,Complex.exp_nat_mul,Complex.exp_sub,hEu,hEz,div_inv_eq_mul]
  congr 2
  rw[div_eq_mul_inv,mul_comm]
lemma compactCenteredLogAction_eq_slice (S L:ℂ→ℂ)(h:ℝ)(z w:ℂ):
    compactCenteredLogAction S L h z w=
      (h:ℂ)*centeredExponentialSlice S z (L z/(Real.sqrt h:ℂ)) w:=by
  dsimp[compactCenteredLogAction,centeredExponentialPhase,centeredExponentialSlice]
  congr 1
  have he:(Complex.I*L z)*(-Complex.I*w/(Real.sqrt h:ℂ))=(L z/(Real.sqrt h:ℂ))*w:=by
    linear_combination -(L z*w/(Real.sqrt h:ℂ))*Complex.I_sq
  rw[he]
lemma unscaled_kernel_compact_charts (a:ℝ)(ha:0<a)(har:a≤ r 0):
    ∃ρ:ℝ,0<ρ∧∀z∈Icc a (r 0),∀h:ℕ,0<h→
      ∃F:ℂ→ℂ,AnalyticOnNhd ℂ F (Metric.ball 0 (ρ*Real.sqrt (h:ℝ))) ∧
        F 0=0 ∧ WP.coeff F 1=0 ∧ WP.coeff F 2=(1/2:ℂ) ∧
        (∀w:ℂ,‖w‖<ρ*Real.sqrt (h:ℝ)→‖F w‖≤‖w‖^2) ∧
        ∀t:ℝ,|t|<ρ*Real.sqrt (h:ℝ)→scaledTiltedKernelFourier z h t=Complex.exp (F ((t:ℂ)*Complex.I)):=by
  obtain ⟨R,S,L,Ω,r,hR,hr,hΩ,hSa,hSd,hExp,hdata,hprop⟩:=unscaled_kernel_compact_phase_data a ha har
  let ρ:ℝ:=min r (Real.pi*Real.sqrt (a/5))
  have hρ:0<ρ:=lt_min hr (mul_pos Real.pi_pos (Real.sqrt_pos.mpr (by positivity)))
  refine ⟨ρ,hρ,?_⟩
  intro z hz h hh
  have hz0:0<z:=ha.trans_le hz.1
  have hzfull:z∈Icc (0:ℝ) (WP.r 0):=⟨hz0.le,hz.2⟩
  have hhR:0<(h:ℝ):=by exact_mod_cast hh
  have hs:0<Real.sqrt (h:ℝ):=Real.sqrt_pos.mpr hhR
  have hsn:(Real.sqrt (h:ℝ):ℂ)≠0:=by exact_mod_cast hs.ne'
  have hv:0<tiltedKernelVariance z:=tiltedKernelVariance_pos z hz0 hz.2
  have hvn:(Real.sqrt (tiltedKernelVariance z):ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  let σ:ℝ:=Real.sqrt ((h:ℝ)*tiltedKernelVariance z)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hhR hv)
  have hσn:(σ:ℂ)≠0:=by exact_mod_cast hσ.ne'
  obtain ⟨hzΩ,hS,hL,hSr,hμ,hvR,hLr,hunit⟩:=hdata z hz
  have hc:L (z:ℂ)/(Real.sqrt (h:ℝ):ℂ)=(σ:ℂ)⁻¹:=by
    rw[hLr]
    dsimp[σ,tiltedKernelVariance]
    rw[Real.sqrt_mul hhR.le,Complex.ofReal_mul,Complex.ofReal_inv]
    field_simp
  have hpoint(w:ℂ)(hw:‖w‖<ρ*Real.sqrt (h:ℝ)):
      ‖-Complex.I*w/(Real.sqrt (h:ℝ):ℂ)‖<r:=by
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hs.le]
    exact ((div_lt_iff₀ hs).mpr hw).trans_le (min_le_left _ _)
  have hjet:=compactCenteredLogAction_jets S L (h:ℝ) hhR (z:ℂ) hS hunit.self_of_nhds
  refine ⟨compactCenteredLogAction S L h (z:ℂ),?_,hjet.1,hjet.2.1,hjet.2.2,?_,?_⟩
  · intro w hw
    have ht:=hprop (z:ℂ) hzΩ _ (hpoint w (by simpa only[Metric.mem_ball,dist_zero_right] using hw))
    exact analyticAt_const.mul (ht.1.comp
      (f:=fun w:ℂ=>((z:ℂ),-Complex.I*w/(Real.sqrt (h:ℝ):ℂ))) (x:=w) (by fun_prop))
  · intro w hw
    have ht:‖centeredExponentialPhase S L ((z:ℂ),-Complex.I*w/(Real.sqrt (h:ℝ):ℂ))‖≤
      ‖-Complex.I*w/(Real.sqrt (h:ℝ):ℂ)‖^2:=(hprop _ hzΩ _ (hpoint w hw)).2
    dsimp only[compactCenteredLogAction]
    rw[norm_mul,Complex.norm_of_nonneg hhR.le]
    apply (mul_le_mul_of_nonneg_left ht hhR.le).trans_eq
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hs.le,div_pow,Real.sq_sqrt hhR.le]
    field_simp
  · intro t ht
    have hvmin:a/5≤ tiltedKernelVariance z:=by
      have hd:=unscaledMean_deriv_lower z hzfull
      dsimp[tiltedKernelVariance]
      nlinarith[hz.1,mul_nonneg hz0.le (sub_nonneg.mpr hd)]
    have hσmin:Real.sqrt (h:ℝ)*Real.sqrt (a/5)≤σ:=by
      rw[←Real.sqrt_mul hhR.le]
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvmin hhR.le)
    have hperiod:ρ*Real.sqrt (h:ℝ)≤ Real.pi*σ:=by
      have hp:=mul_le_mul_of_nonneg_right (min_le_right r (Real.pi*Real.sqrt (a/5))) hs.le
      have hq:=mul_le_mul_of_nonneg_left hσmin Real.pi_pos.le
      dsimp[ρ] at *
      nlinarith
    have htin:t∈Icc (-(Real.pi*σ)) (Real.pi*σ):=abs_le.mp (ht.le.trans hperiod)
    change scaledCenteredFourier _ _ σ t=Complex.exp _
    rw[scaledCenteredFourier,Set.indicator_of_mem htin]
    rw[compactCenteredLogAction_eq_slice,hc]
    have hzR:(z:ℂ)∈Metric.ball (0:ℂ) R:=by
      rw[Metric.mem_ball,dist_zero_right,Complex.norm_of_nonneg hz0.le]
      exact hz.2.trans_lt hR
    have harg:(z:ℂ)*Complex.exp ((σ:ℂ)⁻¹*((t:ℂ)*Complex.I))∈Metric.ball (0:ℂ) R:=by
      rw[Metric.mem_ball,dist_zero_right,norm_mul,Complex.norm_of_nonneg hz0.le,Complex.norm_exp]
      have he:(((σ:ℂ)⁻¹*((t:ℂ)*Complex.I))).re=0:=by simp
      rw[he,Real.exp_zero,mul_one]
      exact hz.2.trans_lt hR
    simp only[Complex.ofReal_natCast]
    rw[centeredKernelSlice_exp S h (z:ℂ) (σ:ℂ)⁻¹ ((t:ℂ)*Complex.I) (hExp _ hzR) (hExp _ harg),hμ]
    have he:(σ:ℂ)⁻¹*((t:ℂ)*Complex.I)=((t/σ:ℝ):ℂ)*Complex.I:=by push_cast;ring
    rw[he]
    change Complex.exp (-(((h:ℝ)*unscaledMean z:ℝ):ℂ)*((t/σ:ℝ):ℂ)*Complex.I)*_=_
    congr 1
    push_cast
    ring
end WP.Coefficients
