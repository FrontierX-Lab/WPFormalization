import WPFormalization.Volumes.ExtractionAmplitude
import WPFormalization.HigherOrder.OptimalMarkedModel
/-! The actual marked amplitudes on one common origin cusp-weight disk.
The coefficient family is the prescribed canonical marked hierarchy composed
with the actual planar inverse and multiplied by the true extraction amplitude.
The common disk and Gevrey-two constants precede every coefficient order.
The parameter-data helper preserves an already chosen optimal model family. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology

def originMarkedAmplitude (P:PsiTheory) (p j:ℕ) (Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ) (z:ℂ):ℂ:=
  Bc z*L j (PositiveConvolution.planarInverse P z)

lemma origin_marked_amplitude_family_of_parameter_data (P:PsiTheory) (p:ℕ)
    (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B:ℝ)
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C) (hB:0<B)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(Bc:ℂ→ℂ)(ρ D:ℝ),0<ρ ∧ ρ<xCritical ∧ 0<D ∧ Bc 0=1 ∧
      (∀x∈Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      (∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ Bc z ∧ ‖Bc z‖≤2 ∧
        PositiveConvolution.planarInverse P z∈Ω) ∧
      (∀j,AnalyticOnNhd ℂ (originMarkedAmplitude P p j Bc L) (Metric.ball 0 ρ)) ∧
      (∀j z,‖z‖≤ρ→‖originMarkedAmplitude P p j Bc L z‖≤D*B^j*(j.factorial:ℝ)^2) ∧
      (∀j x,x∈Icc (0:ℝ) ρ→ originMarkedAmplitude P p j Bc L (x:ℂ)=
        ((extractionB p x*markedCoefficient P p j (inverseY x):ℝ):ℂ)):=by
  obtain ⟨Bc,hBc0,hBcp⟩:=Analysis.extractionB_complex_extension P p
  have hx0:(0:ℝ)∈Ico (0:ℝ) xCritical:=⟨le_rfl,Analysis.xCritical_pos_parameter⟩
  have hBca:AnalyticAt ℂ Bc 0:=by simpa only[Complex.ofReal_zero] using (hBcp 0 hx0).1
  have hYca:AnalyticAt ℂ (PositiveConvolution.planarInverse P) 0:=
    PositiveConvolution.planarInverse_analyticAt P 0 (by simpa using Analysis.xCritical_pos_parameter)
  have hb0:‖Bc 0‖<2:=by rw[hBc0,norm_one];norm_num
  have hbn:∀ᶠz:ℂ in 𝓝 0,‖Bc z‖<2:=hBca.continuousAt.norm.tendsto.eventually (eventually_lt_nhds hb0)
  have hy0:PositiveConvolution.planarInverse P 0∈Ω:=by
    rw[PositiveConvolution.planarInverse_zero P]
    simpa only[Complex.ofReal_zero] using hcover 0 ⟨le_rfl,y₀_pos.le⟩
  have hyn:∀ᶠz:ℂ in 𝓝 0,PositiveConvolution.planarInverse P z∈Ω:=
    hYca.continuousAt.eventually (hΩ.mem_nhds hy0)
  have hball:∀ᶠz:ℂ in 𝓝 0,AnalyticAt ℂ Bc z ∧ ‖Bc z‖<2 ∧
      PositiveConvolution.planarInverse P z∈Ω ∧ ‖z‖<xCritical:=by
    filter_upwards[hBca.eventually_analyticAt,hbn,hyn,
      Metric.ball_mem_nhds (0:ℂ) Analysis.xCritical_pos_parameter] with z hza hzb hzy hz
    exact ⟨hza,hzb,hzy,by simpa only[Metric.mem_ball,dist_zero_right] using hz⟩
  obtain ⟨R,hR,hRball⟩:=Metric.eventually_nhds_iff.mp hball
  let ρ:ℝ:=min (R/2) (xCritical/2)
  have hxc:=Analysis.xCritical_pos_parameter
  have hρ:0<ρ:=lt_min (by positivity) (by positivity)
  have hρR:ρ<R:=lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρx:ρ<xCritical:=lt_of_le_of_lt (min_le_right _ _) (by linarith[Analysis.xCritical_pos_parameter])
  have hlocal:∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ Bc z ∧ ‖Bc z‖≤2 ∧
      PositiveConvolution.planarInverse P z∈Ω ∧ ‖z‖<xCritical:=by
    intro z hz
    have ht:=hRball (show dist z 0<R by simpa only[dist_zero_right] using hz.trans_lt hρR)
    exact ⟨ht.1,ht.2.1.le,ht.2.2⟩
  refine ⟨Bc,ρ,2*C,hρ,hρx,by positivity,hBc0,hBcp,?_,?_,?_,?_⟩
  · intro z hz
    exact ⟨(hlocal z hz).1,(hlocal z hz).2.1,(hlocal z hz).2.2.1⟩
  · intro j z hz
    have hn:‖z‖≤ρ:=by exact (show ‖z‖<ρ from by simpa only[Metric.mem_ball,dist_zero_right] using hz).le
    have hl:=hlocal z hn
    exact hl.1.mul ((hLa j _ hl.2.2.1).comp (PositiveConvolution.planarInverse_analyticAt P z hl.2.2.2))
  · intro j z hz
    have hl:=hlocal z hz
    unfold originMarkedAmplitude
    rw[norm_mul]
    calc
      _≤2*(C*B^j*(j.factorial:ℝ)^2):=mul_le_mul hl.2.1 (hLb j _ hl.2.2.1) (norm_nonneg _) (by norm_num)
      _=_:=by ring
  · intro j x hx
    have hxi:x∈Ico (0:ℝ) xCritical:=⟨hx.1,hx.2.trans_lt hρx⟩
    have hy:inverseY x∈Icc (0:ℝ) y₀:=by
      have hb:=(inverseY_branch x hxi).1
      exact ⟨hb.1,hb.2.le⟩
    unfold originMarkedAmplitude
    rw[(hBcp x hxi).2,PositiveConvolution.planarInverse_ofReal P x hxi,hLr j _ hy,
      Complex.ofReal_mul]
end WP.HigherOrder

namespace WP.HigherOrder
open Set
lemma actual_origin_marked_amplitudes (P:PsiTheory) (p:ℕ) (hp:1≤p):
    ∃(L:ℕ→ℂ→ℂ)(Bc:ℂ→ℂ)(ρ C B:ℝ),
      0<ρ ∧ ρ<xCritical ∧ 0<C ∧ 0<B ∧ Bc 0=1 ∧
      (∀z,L 0 z=1) ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ)) ∧
      (∀x∈Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      (∀j,AnalyticOnNhd ℂ (originMarkedAmplitude P p j Bc L) (Metric.ball 0 ρ)) ∧
      (∀j z,‖z‖≤ρ→‖originMarkedAmplitude P p j Bc L z‖≤C*B^j*(j.factorial:ℝ)^2) ∧
      (∀j x,x∈Icc (0:ℝ) ρ→ originMarkedAmplitude P p j Bc L (x:ℂ)=
        ((extractionB p x*markedCoefficient P p j (inverseY x):ℝ):ℂ)):=by
  obtain ⟨Ω,L,C,B,κ,a,H,hΩ,hcover,hC,hB,hκ,ha,hH,hLa,hL0,hLr,hLb,hmodels⟩:=
    optimal_marked_model_real_comparison P p hp
  obtain ⟨Bc,ρ,D,hρ,hρx,hD,hBc0,hBcp,hlocal,hampA,hampB,hampR⟩:=
    origin_marked_amplitude_family_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  exact ⟨L,Bc,ρ,D,B,hρ,hρx,hD,hB,hBc0,hL0,hLr,hBcp,hampA,hampB,hampR⟩
end WP.HigherOrder
