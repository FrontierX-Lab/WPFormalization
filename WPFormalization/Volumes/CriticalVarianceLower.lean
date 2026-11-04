import WPFormalization.Volumes.CriticalLeadingChart
/-! A genuine variance lower bound near the critical endpoint.
The actual normalization delta^2 L(delta)=1/sqrt(v) and continuity imply
v>=1 after one fixed shrink. Positivity of v is proved from the actual
physical cusp weight and positive Psi derivative. No value is assigned
to the totalized physical first root at the critical endpoint. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma critical_variance_ge_one:
    ∃η:ℝ,0<η ∧ η<y₀ ∧ ∀δ∈Ioo (0:ℝ) η,1≤euler Psi (XR (y₀-δ)):=by
  obtain ⟨d⟩:=exists_criticalGaussianCoordinateData
  have hc:ContinuousAt (fun δ:ℝ=>(δ:ℂ)^2*d.L (δ:ℂ)) 0:=by
    have hL:ContinuousAt (fun δ:ℝ=>d.L (δ:ℂ)) 0:=
      ContinuousAt.comp (f:=fun δ:ℝ=>(δ:ℂ)) (x:=(0:ℝ)) d.L_analytic.continuousAt Complex.continuous_ofReal.continuousAt
    exact ((Complex.continuous_ofReal.continuousAt).pow 2).mul hL
  have hzero:‖((0:ℝ):ℂ)^2*d.L ((0:ℝ):ℂ)‖<(1:ℝ):=by simp
  have hn:∀ᶠδ:ℝ in 𝓝 0,‖(δ:ℂ)^2*d.L (δ:ℂ)‖<1:=
    hc.norm.tendsto.eventually (eventually_lt_nhds hzero)
  obtain ⟨R,hR,hball⟩:=Metric.eventually_nhds_iff.mp (d.physical_normalization.and hn)
  let η:ℝ:=min (R/2) (y₀/2)
  have hη:0<η:=lt_min (by positivity) (div_pos y₀_pos (by norm_num))
  have hηy:η<y₀:=(min_le_right _ _).trans_lt (by linarith[y₀_pos])
  refine ⟨η,hη,hηy,?_⟩
  intro δ hδ
  have hdist:dist δ 0<R:=by
    rw[Real.dist_eq,sub_zero,abs_of_pos hδ.1]
    have ht:δ<R/2:=hδ.2.trans_le (min_le_left _ _)
    linarith
  obtain ⟨hp,hnorm⟩:=hball hdist
  have hY:y₀-δ∈Ico (0:ℝ) y₀:=⟨by linarith[hδ.2],by linarith[hδ.1]⟩
  have hxp:0<XR (y₀-δ):=by
    have ht:=XR_strictMonoOn (show (0:ℝ)∈Iic y₀ from y₀_pos.le) hY.2.le
      (by linarith[hδ.2]:0<y₀-δ)
    simpa only[XR_zero] using ht
  have hxc:XR (y₀-δ)<xCritical:=XR_strictMonoOn hY.2.le (show y₀∈Iic y₀ from Set.mem_Iic.mpr le_rfl) hY.2
  have hv:0<euler Psi (XR (y₀-δ)):=mul_pos hxp (Psi_deriv_pos_interior _ ⟨hxp.le,hxc⟩)
  have hs:0<Real.sqrt (euler Psi (XR (y₀-δ))):=Real.sqrt_pos.mpr hv
  rw[(hp hδ.1).1,Complex.norm_of_nonneg (inv_nonneg.mpr hs.le)] at hnorm
  have ht:=mul_lt_mul_of_pos_right hnorm hs
  rw[inv_mul_cancel₀ hs.ne',one_mul] at ht
  nlinarith[Real.sq_sqrt hv.le]
end WP.Analysis
