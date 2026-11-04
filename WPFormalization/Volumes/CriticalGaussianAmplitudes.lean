import WPFormalization.Volumes.CriticalMorseNormalization
import WPFormalization.Volumes.CriticalAmplitudeUnits
import WPFormalization.HigherOrder.MarkedExtensionProof
/-! The actual marked coefficient amplitudes in common critical Gaussian
coordinates. Every order uses the same complex parameter disk and Gevrey-two
constants; the coefficient family restricts to the original markedCoefficient.
The leading transformed amplitude is one along the entire parameter axis. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma analytic_composition_product_gevrey_two (a y:ℂ × ℂ→ℂ) (y₀:ℂ)
    (ha:AnalyticAt ℂ a (0,0)) (hy:AnalyticAt ℂ y (0,0)) (hy0:y (0,0)=y₀)
    (Ω:Set ℂ) (hΩ:IsOpen Ω) (hcover:y₀∈Ω) (f:ℕ→ℂ→ℂ) (C B:ℝ)
    (hC:0<C) (hB:0<B) (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2) :
    ∃ρ D:ℝ,0<ρ ∧ 0<D ∧
      (∀j,AnalyticOnNhd ℂ (fun p:ℂ × ℂ=>a p*f j (y p)) (Metric.ball 0 ρ)) ∧
      ∀j p,‖p‖<ρ→‖a p*f j (y p)‖≤D*B^j*(j.factorial:ℝ)^2 := by
  let A:ℝ := ‖a (0,0)‖+1
  have hA:0<A := by dsimp [A];positivity
  have hnorm0:‖a (0,0)‖<A := by exact lt_add_one _
  have hnorm:=ha.continuousAt.norm.tendsto.eventually (eventually_lt_nhds hnorm0)
  have hymem:∀ᶠp:ℂ × ℂ in 𝓝 (0,0),y p∈Ω :=
    hy.continuousAt.eventually (hΩ.mem_nhds (by rw [hy0];exact hcover))
  have he:∀ᶠp:ℂ × ℂ in 𝓝 (0,0),
      AnalyticAt ℂ a p ∧ AnalyticAt ℂ y p ∧ y p∈Ω ∧ ‖a p‖≤A := by
    filter_upwards [ha.eventually_analyticAt,hy.eventually_analyticAt,hymem,hnorm] with p hap hyp hp hn
    exact ⟨hap,hyp,hp,hn.le⟩
  obtain ⟨ρ,hρ,hball⟩:=Metric.eventually_nhds_iff.mp he
  refine ⟨ρ,A*C,hρ,mul_pos hA hC,?_,?_⟩
  · intro j p hp
    have ht:=hball (show dist p ((0,0):ℂ × ℂ)<ρ by change dist p (0:ℂ × ℂ)<ρ;simpa only [Metric.mem_ball] using hp)
    exact ht.1.mul ((hf j _ ht.2.2.1).comp ht.2.1)
  · intro j p hp
    have ht:=hball (show dist p ((0,0):ℂ × ℂ)<ρ by change dist p (0:ℂ × ℂ)<ρ;simpa only [dist_zero_right] using hp)
    rw [norm_mul]
    calc _ ≤ A*(C*B^j*(j.factorial:ℝ)^2) :=
          mul_le_mul ht.2.2.2 (hbound j _ ht.2.2.1) (norm_nonneg _) hA.le
         _ = _ := by ring

def CriticalGaussianCoordinateData.modelAmplitude (d:CriticalGaussianCoordinateData)
    (Q:ℂ→ℂ) (p:ℕ) (f:ℕ→ℂ→ℂ) (j:ℕ) (z:ℂ × ℂ) : ℂ :=
  d.kernel.jointAmplitude Q p d.q (z.1,d.U z)*
    f j ((y₀:ℂ)-z.1*d.q (z.1,d.U z))*sndPartial d.U z

lemma CriticalGaussianCoordinateData.modelAmplitude_geometry (d:CriticalGaussianCoordinateData)
    (Q:ℂ→ℂ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1) (p:ℕ) :
    AnalyticAt ℂ (fun z:ℂ × ℂ=>d.kernel.jointAmplitude Q p d.q (z.1,d.U z)*sndPartial d.U z) (0,0) ∧
    AnalyticAt ℂ (fun z:ℂ × ℂ=>(y₀:ℂ)-z.1*d.q (z.1,d.U z)) (0,0) := by
  have hT : AnalyticAt ℂ (fun z:ℂ × ℂ=>(z.1,d.U z)) (0,0) := analyticAt_fst.prod d.U_analytic
  have hT0 : (((0,0):ℂ × ℂ).1,d.U (0,0))=(0,0) := by simp [d.U_zero]
  have hJ : AnalyticAt ℂ (fun z:ℂ × ℂ=>d.kernel.jointAmplitude Q p d.q (z.1,d.U z)) (0,0) :=
    (d.kernel.jointAmplitude_analytic Q hQ hQ0 p d.q d.q_analytic d.q_zero).comp_of_eq hT hT0
  have hq : AnalyticAt ℂ (fun z:ℂ × ℂ=>d.q (z.1,d.U z)) (0,0) :=
    d.q_analytic.comp_of_eq hT hT0
  exact ⟨hJ.mul (sndPartial_analytic d.U (0,0) d.U_analytic),
    analyticAt_const.sub (analyticAt_fst.mul hq)⟩
end WP.Analysis

namespace WP.Analysis
lemma CriticalGaussianCoordinateData.actual_model_amplitudes (d:CriticalGaussianCoordinateData)
    (P:PsiTheory) (p:ℕ) (hp:1≤p) :
    ∃ (Q:ℂ→ℂ) (Ω:Set ℂ) (f:ℕ→ℂ→ℂ) (ρ C B:ℝ),
      AnalyticAt ℂ Q 0 ∧ Q 0=1 ∧
      (∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) ∧
      IsOpen Ω ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      (∀j,AnalyticOnNhd ℂ (f j) Ω) ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)) ∧
      0<ρ ∧ 0<C ∧ 0<B ∧
      (∀j,AnalyticOnNhd ℂ (d.modelAmplitude Q p f j) (Metric.ball 0 ρ)) ∧
      (∀j:ℕ,∀δ w:ℂ,‖δ‖<ρ→‖w‖<ρ→
        ‖d.modelAmplitude Q p f j (δ,w)‖≤C*B^j*(j.factorial:ℝ)^2) ∧
      (∀δ:ℂ,‖δ‖<ρ→d.modelAmplitude Q p f 0 (δ,0)=1) := by
  obtain ⟨Q,hQ,hQ0,hQphys⟩ := exists_criticalThetaUnit
  obtain ⟨C₀,B,hC₀,hB,Ω,aC,f,hΩ,hcover,hf,hrest,hbound⟩ :=
    HigherOrder.markedCoefficient_common_complex_gevrey_two P p hp
  let a:ℂ × ℂ→ℂ := fun z=>d.kernel.jointAmplitude Q p d.q (z.1,d.U z)*sndPartial d.U z
  let y:ℂ × ℂ→ℂ := fun z=>(y₀:ℂ)-z.1*d.q (z.1,d.U z)
  obtain ⟨ha,hy⟩ := d.modelAmplitude_geometry Q hQ hQ0 p
  have hy0 : y (0,0)=(y₀:ℂ) := by simp [y]
  have hfb : ∀j z,z∈Ω→‖f j z‖≤C₀*B^j*(j.factorial:ℝ)^2 := by
    intro j z hz
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hbound j z hz)
  obtain ⟨ρ₀,C,hρ₀,hC,hafa,hafb⟩ := analytic_composition_product_gevrey_two a y y₀ ha hy hy0
    Ω hΩ (hcover _ ⟨y₀_pos.le,le_rfl⟩) f C₀ B hC₀ hB (fun j=>(hf j).2) hfb
  have heq (j:ℕ) : d.modelAmplitude Q p f j=(fun z:ℂ × ℂ=>a z*f j (y z)) := by
    funext z
    dsimp only [CriticalGaussianCoordinateData.modelAmplitude,a,y]
    ring
  have hmoda (j:ℕ) : AnalyticOnNhd ℂ (d.modelAmplitude Q p f j) (Metric.ball 0 ρ₀) := by
    rw [heq]
    exact hafa j
  have h0a : AnalyticAt ℂ (fun δ:ℂ=>d.modelAmplitude Q p f 0 (δ,0)) 0 :=
    (hmoda 0 (0,0) (by change (0:ℂ × ℂ)∈Metric.ball 0 ρ₀;exact Metric.mem_ball_self hρ₀)).comp
      (f:=fun δ:ℂ=>(δ,(0:ℂ))) (analyticAt_id.prod analyticAt_const)
  have hzero : ∀ᶠδ:ℂ in 𝓝 0,d.modelAmplitude Q p f 0 (δ,0)=1 := by
    apply complex_germ_identity_of_real_right _ _ h0a analyticAt_const
    have hc : Tendsto (fun δ:ℝ=>(δ:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have hca : Tendsto (fun δ:ℝ=>((δ:ℂ),(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) :=
      Complex.continuous_ofReal.continuousAt.prodMk continuous_const.continuousAt |>.tendsto
    filter_upwards [d.kernel.physical,hc.eventually d.U_axis,hc.eventually d.q_axis,
      hc.eventually d.U_axis_deriv,hca.eventually d.U_analytic.eventually_analyticAt,
      hc.eventually (d.kernel.jointAmplitude_axis Q hQ hQ0 p d.q d.q_axis)]
      with δ hphys hU0 hq0 hD hUδ hAmp hδ
    have hY : y₀-δ∈Icc (0:ℝ) y₀ := ⟨by linarith [(hphys hδ).1],by linarith⟩
    have hf0 : f 0 ((y₀:ℂ)-(δ:ℂ))=1 := by
      rw [←Complex.ofReal_sub,(hrest 0 _ hY).2,HigherOrder.markedCoefficient_zero]
      rfl
    change d.modelAmplitude Q p f 0 ((δ:ℂ),0)=1
    rw [CriticalGaussianCoordinateData.modelAmplitude,hU0,hq0,mul_one,hf0,hAmp,
      sndPartial_eq_deriv d.U ((δ:ℂ),0) hUδ,hD]
    ring
  obtain ⟨ρ₁,hρ₁,hzball⟩ := Metric.eventually_nhds_iff.mp hzero
  let ρ:ℝ := min ρ₀ ρ₁
  have hρ:0<ρ := lt_min hρ₀ hρ₁
  have hρ0:ρ≤ρ₀ := min_le_left _ _
  have hρ1:ρ≤ρ₁ := min_le_right _ _
  refine ⟨Q,Ω,f,ρ,C,B,hQ,hQ0,hQphys,hΩ,hcover,(fun j=>(hf j).2),
    (fun j Y hY=>(hrest j Y hY).2),hρ,hC,hB,?_,?_,?_⟩
  · intro j z hz
    exact hmoda j z (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le hρ0))
  · intro j δ w hδ hw
    rw [heq]
    apply hafb
    simpa only [Prod.norm_def,max_lt_iff] using And.intro (hδ.trans_le hρ0) (hw.trans_le hρ0)
  · intro δ hδ
    exact hzball (by simpa only [dist_zero_right] using hδ.trans_le hρ1)
end WP.Analysis
