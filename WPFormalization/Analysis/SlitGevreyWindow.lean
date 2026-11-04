import WPFormalization.Analysis.SlitDiskComparison
/-! Quantitative selection of the quarter-power central window.
One fixed window has T^2 proportional to sqrt(h). Its complex growth is
absorbed by the real Gevrey-two optimal exponential error after the slit
transfer, and the whole transfer disk stays inside the actual analytic disk.
All constants precede the scale h. This is a proved numerical lemma. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma slit_gevrey_two_window_constants (R D E C a:ℝ)
    (hR:0<R)(hD:0<D)(hE:0<E)(hC:0<C)(ha:0<a):
    ∃τ b C0 H:ℝ,0<τ ∧ 0<b ∧ 0<C0 ∧ 0<H ∧
      ∀h:ℝ,H≤h→0<h ∧
        2*C*Real.exp (-a*Real.sqrt h)≤1/2 ∧
        16*(τ*Real.sqrt (Real.sqrt h))<R*Real.sqrt h ∧
        4*Real.sqrt (2*C*Real.exp (-a*Real.sqrt h))*
          (D*Real.exp (E*(16*(τ*Real.sqrt (Real.sqrt h)))^2))≤
            C0*Real.exp (-b*Real.sqrt h):=by
  let τ:ℝ:=min 1 (Real.sqrt (a/(2048*E)))
  have hτ:0<τ:=lt_min zero_lt_one (Real.sqrt_pos.mpr (by positivity))
  have hτsqrt:τ≤Real.sqrt (a/(2048*E)):=min_le_right _ _
  have hτ2:τ^2≤a/(2048*E):=by
    exact (pow_le_pow_left₀ hτ.le hτsqrt 2).trans_eq (Real.sq_sqrt (by positivity))
  have hbudget:256*E*τ^2≤a/8:=by
    have ht:=(le_div_iff₀ (by positivity:0<2048*E)).mp hτ2
    nlinarith
  have hlin:Tendsto (fun h:ℝ=>a*Real.sqrt h) atTop atTop:=
    Filter.Tendsto.const_mul_atTop ha Real.tendsto_sqrt_atTop
  have heps:Tendsto (fun h:ℝ=>2*C*Real.exp (-a*Real.sqrt h)) atTop (𝓝 (0:ℝ)):=by
    have ht:=((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin))).const_mul (2*C)
    simpa only[Function.comp_def,neg_mul,mul_zero] using ht
  have hq:Tendsto (fun h:ℝ=>Real.sqrt (Real.sqrt h)) atTop atTop:=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop
  obtain ⟨He,hHe⟩:=eventually_atTop.1 (heps.eventually (eventually_lt_nhds (by norm_num:(0:ℝ)<1/2)))
  obtain ⟨Hr,hHr⟩:=eventually_atTop.1 (hq.eventually (eventually_gt_atTop (16*τ/R)))
  let H:ℝ:=max 1 (max He Hr)
  let C0:ℝ:=4*Real.sqrt (2*C)*D
  have hH:0<H:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC0:0<C0:=by dsimp[C0];positivity
  refine ⟨τ,a/4,C0,H,hτ,by positivity,hC0,hH,?_⟩
  intro h hh
  have hh1:1≤h:=(le_max_left _ _).trans hh
  have hhp:0<h:=lt_of_lt_of_le zero_lt_one hh1
  have he:2*C*Real.exp (-a*Real.sqrt h)<1/2:=hHe h (((le_max_left _ _).trans (le_max_right _ _)).trans hh)
  have hqt:16*τ/R<Real.sqrt (Real.sqrt h):=hHr h (((le_max_right _ _).trans (le_max_right _ _)).trans hh)
  have hqp:0<Real.sqrt (Real.sqrt h):=Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hhp)
  have hqsq:(Real.sqrt (Real.sqrt h))^2=Real.sqrt h:=Real.sq_sqrt (Real.sqrt_nonneg h)
  have h16:16*(τ*Real.sqrt (Real.sqrt h))<R*Real.sqrt h:=by
    have hlt:16*τ<R*Real.sqrt (Real.sqrt h):=by
      simpa only[mul_comm] using (div_lt_iff₀ hR).mp hqt
    have ht:=mul_lt_mul_of_pos_right hlt hqp
    calc
      _<R*Real.sqrt (Real.sqrt h)*Real.sqrt (Real.sqrt h):=by nlinarith[ht]
      _=R*(Real.sqrt (Real.sqrt h))^2:=by ring
      _=R*Real.sqrt h:=by rw[hqsq]
  refine ⟨hhp,he.le,h16,?_⟩
  have hsqrt:Real.sqrt (2*C*Real.exp (-a*Real.sqrt h))=
      Real.sqrt (2*C)*Real.exp (-a*Real.sqrt h/2):=by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw[mul_pow,Real.sq_sqrt (by positivity:0≤2*C)]
    have ht:(Real.exp (-a*Real.sqrt h/2))^2=Real.exp (-a*Real.sqrt h):=by
      rw[pow_two,←Real.exp_add]
      congr 1
      ring
    rw[ht]
  have hscale:E*(16*(τ*Real.sqrt (Real.sqrt h)))^2=256*E*τ^2*Real.sqrt h:=by
    calc
      _=256*E*τ^2*(Real.sqrt (Real.sqrt h))^2:=by ring
      _=_:=by rw[hqsq]
  rw[hsqrt]
  calc
    _=C0*Real.exp (-a*Real.sqrt h/2+E*(16*(τ*Real.sqrt (Real.sqrt h)))^2):=by
      rw[Real.exp_add]
      dsimp[C0]
      ring
    _≤C0*Real.exp (-(a/4)*Real.sqrt h):=by
      apply mul_le_mul_of_nonneg_left _ hC0.le
      apply Real.exp_le_exp.mpr
      rw[hscale]
      nlinarith[mul_le_mul_of_nonneg_right hbudget (Real.sqrt_nonneg h)]
end WP.Analysis
