import WPFormalization.Tight.ConnectedLeadingComparison
import WPFormalization.Tight.ConnectedFourierInversion
import WPFormalization.Tight.ConnectedTilt
import WPFormalization.Tight.ConnectedLengthModulus
import WPFormalization.Volumes.UniformLeadingGaussianCharts
import WPFormalization.Analysis.ScaledGaussianModelError
noncomputable section
namespace WP.TightConnected
open Set Filter Complex
open scoped Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
lemma tight_gaussian_chart_core_error (P:PsiTheory)(g p:ℕ)(hp:1 ≤ p)(hs:Stable g p)
    (Lphys:Fin p→ℝ)(δ:ℝ)(hδ:0<δ)(hδsmall:7*δ ≤ 1/2)
    (x μ σ ρ C D m T:ℝ)(hx:x∈Ico (0:ℝ) xCritical)
    (hrel0:|tightLeadingError P g p Lphys (tightParameterScale (inverseY x)) x| ≤ 7*δ)
    (hreltilt:∀u:ℝ,|u|<16*T→
      |tightLeadingError P g p Lphys (tightParameterScale (inverseY x)) (x*Real.exp (u/σ))| ≤ 7*δ)
    (hρ:0<ρ)(hC:0<C)(hD:0<D)(hm:0 < m)(hT:1 ≤ T)
    (hwindow:32*T ≤ ρ*Real.sqrt m)(hsmall:4*C*T^3/(ρ*Real.sqrt m) ≤ 1)
    (L A:ℂ→ℂ)
    (hLa:AnalyticOnNhd ℂ L (Metric.ball 0 (ρ*Real.sqrt m)))
    (hAa:AnalyticOnNhd ℂ A (Metric.ball 0 (ρ*Real.sqrt m)))
    (hL0:L 0=0)(hL1:WP.coeff L 1=0)(hL2:WP.coeff L 2=(1/2:ℂ))(hA0:A 0=1)
    (hbL:∀w:ℂ,‖w‖<ρ*Real.sqrt m→‖L w‖ ≤ C*‖w‖^2)
    (hbA:∀w:ℂ,‖w‖<ρ*Real.sqrt m→‖A w‖ ≤ D)
    (htrace:∀u:ℝ,|u|<ρ*Real.sqrt m→
      x*Real.exp (u/σ)∈Ioo (0:ℝ) xCritical ∧
      Complex.exp (L (u:ℂ))*A (u:ℂ)=
        ((Real.exp (-μ*u/σ)*markedModel g p (inverseY (x*Real.exp (u/σ)))/
          markedModel g p (inverseY x):ℝ):ℂ))
    (t:ℝ)(ht:|t| ≤ T):
    ‖centeredTightGenerating P g p Lphys x μ σ ((t:ℂ)*Complex.I)-Complex.exp (-(t:ℂ)^2/2)‖ ≤
      4*D*Real.sqrt (7*δ)*Real.exp (256*C*T^2)+
        (8*C*D*T^3+4*D*T)/(ρ*Real.sqrt m):=by
  let M:ℂ→ℂ:=fun z=>Complex.exp (L z)*A z
  let G:ℝ:=D*Real.exp (256*C*T^2)
  have hTp:0<T:=zero_lt_one.trans_le hT
  have hRadius:16*T<ρ*Real.sqrt m:=by linarith
  have hMs:AnalyticOnNhd ℂ M (Metric.ball 0 (16*T)):=by
    intro z hz
    have hn:‖z‖<16*T:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
    have hzr:z∈Metric.ball (0:ℂ) (ρ*Real.sqrt m):=by
      simpa only[Metric.mem_ball,dist_zero_right] using hn.trans hRadius
    exact (hLa z hzr).cexp.mul (hAa z hzr)
  have hMb:∀z:ℂ,‖z‖<16*T→‖M z‖ ≤ G:=by
    intro z hz
    have hzR:‖z‖<ρ*Real.sqrt m:=hz.trans hRadius
    have hnorm:‖Complex.exp (L z)‖ ≤ Real.exp (256*C*T^2):=by
      rw[Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hl: (L z).re ≤ C*‖z‖^2:=(Complex.re_le_norm _).trans (hbL z hzR)
      have hsq:‖z‖^2 ≤ (16*T)^2:=by nlinarith[norm_nonneg z]
      nlinarith[mul_le_mul_of_nonneg_left hsq hC.le]
    dsimp only[M,G]
    rw[norm_mul]
    exact (mul_le_mul hnorm (hbA z hzR) (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)
  have htilt:∀z:ℂ,‖z‖<16*T→x*Real.exp (z.re/σ)∈Ico (0:ℝ) xCritical:=by
    intro z hz
    have hr:|z.re|<ρ*Real.sqrt m:=(Complex.abs_re_le_norm z).trans_lt (hz.trans hRadius)
    exact ⟨(htrace z.re hr).1.1.le,(htrace z.re hr).1.2⟩
  have hMtrace:∀u:ℝ,|u|<16*T→M (u:ℂ)=
      ((Real.exp (-μ*u/σ)*markedModel g p (inverseY (x*Real.exp (u/σ)))/
        markedModel g p (inverseY x):ℝ):ℂ):=by
    intro u hu
    exact (htrace u (hu.trans hRadius)).2
  have hw:‖(t:ℂ)*Complex.I‖ ≤ 3*T/2:=by
    rw[norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    linarith
  have hcomp:=tight_leading_slit_comparison P g p hp hs Lphys (tightParameterScale (inverseY x)) δ
    hδ hδsmall x μ σ T G hx hTp
    (by dsimp[G];positivity) hrel0 hreltilt M hMs hMb htilt hMtrace _ hw
  have hmodel:=Analysis.scaled_gaussian_model_core_error L A ρ C D m T hρ hC hD hm hT hwindow hsmall
    hLa hAa hL0 hL1 hL2 hA0 hbL hbA t ht
  have hsum:=norm_sub_le_norm_sub_add_norm_sub
    (centeredTightGenerating P g p Lphys x μ σ ((t:ℂ)*Complex.I)) (M ((t:ℂ)*Complex.I))
    (Complex.exp (-(t:ℂ)^2/2))
  apply (hsum.trans (add_le_add hcomp hmodel)).trans_eq
  dsimp[G]
  ring


lemma tight_characteristic_gaussian_core_tendsto
    (P : PsiTheory) (p : ℕ) (hp : 1  ≤  p) (L₀ : ℝ) (hL₀ : 0  ≤  L₀)
    (gs : ℕ → ℕ) (hgs : Tendsto gs atTop atTop)
    (xs : ℕ → ℝ) (hxs : ∀ j, xs j ∈ Ioo (0 : ℝ) xCritical)
    (Ls : ℕ → Fin p → ℝ) (hLs : ∀ j i, 0  ≤  Ls j i ∧ tightParameterScale (inverseY (xs j))*Ls j i  ≤  L₀)
    (hmean : Tendsto (fun j => (complexity (gs j) p : ℝ)*Psi (xs j)) atTop atTop) :
    ∀ T : ℝ, 1  ≤  T → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      ∀ t : ℝ, |t|  ≤  T →
        ‖scaledTightFourier P (gs j) p (Ls j) (xs j) t -
          Complex.exp (-(t : ℂ)^2/2)‖  ≤  ε := by
  obtain ⟨ρ,C,D,hρ,hC,hD,hcharts⟩ := uniform_actual_leading_gaussian_charts P p hp
  obtain ⟨Cb,E,H,hCb,hE,hH,hEH,hleading⟩ := tight_leading_relative_error P p hp (2*L₀) (by positivity)
  have hhT : Tendsto (fun j => (complexity (gs j) p : ℝ)) atTop atTop :=
    Analysis.complexity_real_tendsto_atTop p |>.comp hgs
  let m : ℕ → ℝ := fun j => min (complexity (gs j) p : ℝ)
    ((complexity (gs j) p : ℝ)*Psi (xs j))
  have hmT : Tendsto m atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hhT.eventually_ge_atTop b, hmean.eventually_ge_atTop b] with j hj hk
    exact le_min hj hk
  have hradT : Tendsto (fun j => ρ*Real.sqrt (m j)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hmT).const_mul_atTop hρ
  have hgReal : Tendsto (fun j => (gs j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hgs
  intro T hT ε hε
  let G : ℝ := D*Real.exp (256*C*T^2)
  have hG : 0 < G := by dsimp [G]; positivity
  let K : ℝ := ε/(8*G)
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := min (1/14) (K^2/7)
  have hδ : 0 < δ := lt_min (by norm_num) (by dsimp [K]; positivity)
  have hδ1 : δ  ≤  1 := (min_le_left _ _).trans (by norm_num)
  have hδsmall : 7*δ  ≤  1/2 := by have := min_le_left (1/14:ℝ) (K^2/7); change δ  ≤  _ at this; linarith
  have hδK : 7*δ  ≤  K^2 := by have := min_le_right (1/14:ℝ) (K^2/7); change δ  ≤  _ at this; linarith
  have hsqrt : Real.sqrt (7*δ)  ≤  K := (Real.sqrt_le_iff).mpr ⟨hK.le,hδK⟩
  have hcompε : 4*D*Real.sqrt (7*δ)*Real.exp (256*C*T^2)  ≤  ε/2 := by
    have hh := mul_le_mul_of_nonneg_left hsqrt (show 0  ≤  4*G by positivity)
    have he : 4*G*K=ε/2 := by dsimp [K]; field_simp; ring
    dsimp [G] at hh he
    nlinarith only [hh,he]
  -- Only scaled lengths are confined to a compact box. The real physical
  -- lengths stay fixed during each generating-function evaluation.
  obtain ⟨η,hη,hfactor⟩ := connected_scaled_factor_uniform_relative_continuity p L₀ δ hδ
  let τ : ℝ := min (1/2) (η/2)
  have hτ : 0<τ := lt_min (by norm_num) (half_pos hη)
  have hτhalf : τ ≤ 1/2 := min_le_left _ _
  have hτη : τ ≤ η/2 := min_le_right _ _
  obtain ⟨M,hM,htiltmod⟩ := connected_tight_scale_tilt_uniform (16*T) τ (by linarith) hτ
  have hCbzero : Tendsto (fun j => Cb/(gs j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hgReal
  have hEzero : Tendsto (fun j => E/(complexity (gs j) p : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hhT
  have hmodelzero : Tendsto (fun j => (8*C*D*T^3+4*D*T)/(ρ*Real.sqrt (m j))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hradT
  filter_upwards [hgs.eventually_ge_atTop 2, hhT.eventually_ge_atTop H,
    hmT.eventually_ge_atTop M,hmT.eventually_gt_atTop 0,
    hradT.eventually_ge_atTop (32*T), hradT.eventually_ge_atTop (4*C*T^3),
    hCbzero.eventually (gt_mem_nhds hδ),hEzero.eventually (gt_mem_nhds hδ),
    hmodelzero.eventually (gt_mem_nhds (half_pos hε))] with j hj hHj hMj hmj hwin hsm hCj hEj hmodelj
  let g := gs j
  let x := xs j
  let h : ℝ := complexity g p
  let σ : ℝ := Real.sqrt (h*euler Psi x)
  have hs : Stable g p := by dsimp [g]; unfold Stable; omega
  have hh : 0 < h := hH.trans_le hHj
  obtain ⟨hchart,hperiod⟩ := hcharts g hs hh x (hxs j) hmj
  rcases hchart with ⟨Alog,Amp,hLa,hL0,hL1,hL2,hLb,hAa,hA0,hAb,htrace⟩
  have hsmall : 4*C*T^3/(ρ*Real.sqrt (m j))  ≤  1 :=
    (div_le_one (mul_pos hρ (Real.sqrt_pos.mpr hmj))).mpr hsm
  have hR : 16*T < ρ*Real.sqrt (m j) := by linarith
  have hα : 0<tightParameterScale (inverseY x) :=
    tightParameterScale_pos _ (inverseY_branch x ⟨(hxs j).1.le,(hxs j).2⟩).1
  have hLpos : ∀i,0 ≤ Ls j i := fun i=>(hLs j i).1
  have hLscaled : ∀i,tightParameterScale (inverseY x)*Ls j i ≤ 2*L₀ := by
    intro i
    exact (hLs j i).2.trans (by linarith)
  have he0 : |tightLeadingError P g p (Ls j) (tightParameterScale (inverseY x)) x|  ≤  7*δ := by
    apply hleading g (by omega) hs hHj (Ls j) hLpos (tightParameterScale (inverseY x)) x
      ⟨(hxs j).1.le,(hxs j).2⟩ hLscaled δ hδ.le hδ1 hCj.le hEj.le
    have hb : (∏i,boundaryFactor 0 (tightParameterScale (inverseY x)*Ls j i))≠0 :=
      (Finset.prod_pos (fun i _=>boundaryFactor_pos _ _)).ne'
    rw [div_self hb,sub_self,abs_zero]
    exact hδ.le
  have hetilt : ∀ u : ℝ, |u|<16*T →
      |tightLeadingError P g p (Ls j) (tightParameterScale (inverseY x)) (x*Real.exp (u/σ))| ≤ 7*δ := by
    intro u hu
    have hxt := (htrace u (hu.trans hR)).1
    have hd := htiltmod h hh x (hxs j) hMj u hu.le hxt
    let q : ℝ := tightParameterScale (inverseY (x*Real.exp (u/σ)))/tightParameterScale (inverseY x)
    have hq0 : 0<q := div_pos (tightParameterScale_pos _ (inverseY_branch _ ⟨hxt.1.le,hxt.2⟩).1) hα
    have hq2 : q ≤ 2 := by
      change |q-1| ≤ τ at hd
      have he := (abs_le.mp hd).2
      linarith
    have heq (i:Fin p) : q*(tightParameterScale (inverseY x)*Ls j i)=
        tightParameterScale (inverseY (x*Real.exp (u/σ)))*Ls j i := by
      dsimp [q]
      field_simp
    have hfac := hfactor q ⟨hq0.le,hq2⟩
      (fun i=>tightParameterScale (inverseY x)*Ls j i)
      (fun i=>⟨mul_nonneg hα.le (hLpos i),(hLs j i).2⟩)
      (hd.trans_lt (hτη.trans_lt (half_lt_self hη)))
    simp_rw [heq] at hfac
    have hscaled : ∀i,tightParameterScale (inverseY (x*Real.exp (u/σ)))*Ls j i ≤ 2*L₀ := by
      intro i
      rw [←heq i]
      exact (mul_le_mul_of_nonneg_right hq2 (mul_nonneg hα.le (hLpos i))).trans
        (mul_le_mul_of_nonneg_left (hLs j i).2 (by norm_num : 0 ≤ (2:ℝ)))
    exact hleading g (by omega) hs hHj (Ls j) hLpos (tightParameterScale (inverseY x)) _
      ⟨hxt.1.le,hxt.2⟩ hscaled δ hδ.le hδ1 hCj.le hEj.le hfac
  have htrace' : ∀ u : ℝ, |u| < ρ*Real.sqrt (m j) →
      x*Real.exp (u/σ) ∈ Ioo (0:ℝ) xCritical ∧
      Complex.exp (Alog (u:ℂ))*Amp (u:ℂ)=
        ((Real.exp (-(h*Psi x)*u/σ)*markedModel g p (inverseY (x*Real.exp (u/σ)))/
          markedModel g p (inverseY x):ℝ):ℂ) := by
    intro u hu
    have hr := htrace u hu
    dsimp only at hr
    refine ⟨hr.1,hr.2.trans ?_⟩
    rw [show -((h*Psi x:ℝ):ℂ)*(u:ℂ)/(σ:ℂ)=
      ((-(h*Psi x)*u/σ:ℝ):ℂ) by push_cast; ring,←Complex.ofReal_exp]
    push_cast
    ring
  intro t ht
  have htp : |t|  ≤  Real.pi*σ := by
    have hTr : T  ≤  ρ*Real.sqrt (m j) := by linarith
    exact ht.trans (hTr.trans hperiod)
  rw [scaledTightFourier_eq_centered P g p (Ls j) x t htp]
  have he := tight_gaussian_chart_core_error P g p hp hs (Ls j) δ hδ hδsmall
    x (h*Psi x) σ ρ C D (m j) T ⟨(hxs j).1.le,(hxs j).2⟩ he0 hetilt
    hρ hC hD hmj hT hwin hsmall Alog Amp hLa hAa hL0 hL1 hL2 hA0 hLb hAb htrace' t ht
  exact he.trans (by linarith only [hcompε,hmodelj])

end WP.TightConnected
