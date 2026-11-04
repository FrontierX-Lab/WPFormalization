import WPFormalization.Volumes.CriticalGaussianCoordinates
/-! The actual critical Morse inverse has unit angle derivative for every
nearby complex parameter. Quadratic Hadamard factorization then gives a single
parameter-independent O(w^2) displacement bound, including the critical point. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma sndPartial_two_eq_iteratedDeriv (F:ℂ × ℂ→ℂ) (p:ℂ × ℂ)
    (hF:AnalyticAt ℂ F p) :
    sndPartial (sndPartial F) p=iteratedDeriv 2 (fun u:ℂ=>F (p.1,u)) p.2 := by
  have hc : ContinuousAt (fun u:ℂ=>(p.1,u)) p.2 := by fun_prop
  have he : deriv (fun u:ℂ=>F (p.1,u)) =ᶠ[𝓝 p.2]
      (fun u:ℂ=>sndPartial F (p.1,u)) := by
    filter_upwards [hc.tendsto.eventually hF.eventually_analyticAt] with u hu
    exact (sndPartial_eq_deriv F (p.1,u) hu).symm
  rw [iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
  exact sndPartial_eq_deriv (sndPartial F) p (sndPartial_analytic F p hF)

lemma normalized_quadratic_conjugacy_deriv_sq (F U:ℂ→ℂ)
    (hF:AnalyticAt ℂ F 0) (hU:AnalyticAt ℂ U 0)
    (hF0:F 0=0) (hF1:deriv F 0=0) (hF2:iteratedDeriv 2 F 0=-1)
    (hU0:U 0=0) (hconj:∀ᶠw:ℂ in 𝓝 0,F (U w)=-w^2/2) :
    (deriv U 0)^2=1 := by
  obtain ⟨G,hG,hG0,hGF⟩ := complex_analytic_quadratic_factor F hF hF0 hF1
  obtain ⟨V,hV,hV0,hVF⟩ := complex_analytic_linear_factor U hU hU0
  have hGv : G 0=-(1/2:ℂ) := by rw [hG0,hF2];ring
  have hUt : Tendsto U (𝓝 0) (𝓝 (0:ℂ)) := by simpa only [hU0] using hU.continuousAt.tendsto
  have hGu : AnalyticAt ℂ (fun w:ℂ=>G (U w)) 0 := by
    have hGa : AnalyticAt ℂ G (U 0) := by simpa only [hU0] using hG
    exact hGa.comp hU
  have ha : AnalyticAt ℂ (fun w:ℂ=>(V w)^2*G (U w)) 0 := (hV.pow 2).mul hGu
  have he : (fun w:ℂ=>(V w)^2*G (U w)) =ᶠ[𝓝 0] (fun _=>-(1/2:ℂ)) := by
    apply (ha.frequently_eq_iff_eventually_eq analyticAt_const).mp
    have hp : (fun w:ℂ=>(V w)^2*G (U w)) =ᶠ[𝓝[≠] 0] (fun _=>-(1/2:ℂ)) := by
      filter_upwards [hconj.filter_mono nhdsWithin_le_nhds,
        (hUt.eventually hGF).filter_mono nhdsWithin_le_nhds,
        hVF.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hgf hvf hn
      have hwn : w≠0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hn
      rw [hgf,hvf,mul_pow] at hw
      apply mul_left_cancel₀ (pow_ne_zero 2 hwn)
      rw [hvf]
      linear_combination hw
    exact hp.frequently
  have hzero := he.self_of_nhds
  change (V 0)^2*G (U 0)=-(1/2:ℂ) at hzero
  rw [hU0,hGv,hV0] at hzero
  linear_combination -2*hzero

lemma CriticalGaussianCoordinateData.U_axis_deriv (d:CriticalGaussianCoordinateData) :
    ∀ᶠδ:ℂ in 𝓝 0,deriv (fun w:ℂ=>d.U (δ,w)) 0=1 := by
  let F:ℂ × ℂ→ℂ := d.kernel.centeredPhase d.L d.q
  have hF : AnalyticAt ℂ F (0,0) :=
    d.kernel.centeredPhase_analytic d.L d.q d.L_analytic d.q_analytic d.q_zero
  have hns : ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      (δ:ℂ)^2*d.L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ) := by
    filter_upwards [d.physical_normalization] with δ hδ hpos
    exact (hδ hpos).1
  have hsq := d.kernel.normalization_square d.L d.L_analytic hns
  have hjets := d.kernel.centeredPhase_jets d.L d.q d.L_analytic d.q_analytic d.q_zero d.q_axis d.q_fold hsq
  have hDU0 : sndPartial d.U (0,0)=1 :=
    (sndPartial_eq_deriv d.U (0,0) d.U_analytic).trans d.U_deriv
  have hDUne : ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),sndPartial d.U p≠-1 :=
    (sndPartial_analytic d.U (0,0) d.U_analytic).continuousAt.eventually_ne (by rw [hDU0];norm_num)
  have ht : Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) :=
    (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
  filter_upwards [hjets,ht.eventually hF.eventually_analyticAt,ht.eventually d.U_analytic.eventually_analyticAt,
    ht.eventually d.phase_identity.eventually_nhds,d.U_axis,ht.eventually hDUne]
    with δ hjet hFδ hUδ hconjloc hU0 hne
  have hc : ContinuousAt (fun w:ℂ=>(δ,w)) 0 := by fun_prop
  have hconj : ∀ᶠw:ℂ in 𝓝 0,F (δ,d.U (δ,w))=-w^2/2 := hc.tendsto.eventually hconjloc
  have hF1 : deriv (fun u:ℂ=>F (δ,u)) 0=0 := by
    rw [←sndPartial_eq_deriv F (δ,0) hFδ]
    exact hjet.2.1
  have hF2 : iteratedDeriv 2 (fun u:ℂ=>F (δ,u)) 0=-1 :=
    (sndPartial_two_eq_iteratedDeriv F (δ,0) hFδ).symm.trans hjet.2.2
  have hsqD := normalized_quadratic_conjugacy_deriv_sq (fun u:ℂ=>F (δ,u))
    (fun w:ℂ=>d.U (δ,w)) hFδ.curry_right hUδ.curry_right hjet.1 hF1 hF2 hU0 hconj
  have hDerNe : deriv (fun w:ℂ=>d.U (δ,w)) 0≠-1 := by
    rw [←sndPartial_eq_deriv d.U (δ,0) hUδ]
    exact hne
  have hm : (deriv (fun w:ℂ=>d.U (δ,w)) 0-1)*(deriv (fun w:ℂ=>d.U (δ,w)) 0+1)=0 := by
    linear_combination hsqD
  rcases mul_eq_zero.mp hm with h | h
  · exact sub_eq_zero.mp h
  · exact False.elim (hDerNe (by linear_combination h))
end WP.Analysis

namespace WP.Analysis
lemma analytic_parameter_quadratic_bound (F:ℂ × ℂ→ℂ)
    (hF:AnalyticAt ℂ F (0,0)) (haxis:∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0)
    (hderiv:∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>F (δ,u)) 0=0) :
    ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀δ u:ℂ,‖δ‖<ρ→‖u‖<ρ→‖F (δ,u)‖≤C*‖u‖^2 := by
  obtain ⟨H,hH,hfactor⟩ := exists_analytic_parameter_square_factor F hF haxis hderiv
  let C:ℝ := ‖H (0,0)‖+1
  have hC : 0<C := by dsimp [C];positivity
  have hnorm0 : ‖H (0:ℂ × ℂ)‖<C := by
    change ‖H (0,0)‖<‖H (0,0)‖+1
    exact lt_add_one _
  have hnorm : ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),‖H p‖<C :=
    hH.continuousAt.norm.tendsto.eventually (eventually_lt_nhds hnorm0)
  have he : ∀ᶠp:ℂ × ℂ in 𝓝 (0,0),‖F p‖≤C*‖p.2‖^2 := by
    filter_upwards [hfactor,hnorm] with p hp hnp
    rw [hp,norm_mul,norm_pow,mul_comm C]
    exact mul_le_mul_of_nonneg_left hnp.le (pow_nonneg (norm_nonneg _) 2)
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ρ,C,hρ,hC,?_⟩
  intro δ u hδ hu
  exact hball (by simpa [dist_eq_norm,Prod.norm_def,max_lt_iff] using And.intro hδ hu)

lemma CriticalGaussianCoordinateData.U_quadratic_bound (d:CriticalGaussianCoordinateData) :
    ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀δ w:ℂ,‖δ‖<ρ→‖w‖<ρ→
      ‖d.U (δ,w)-w‖≤C*‖w‖^2 := by
  let F:ℂ × ℂ→ℂ := fun p=>d.U p-p.2
  have hF : AnalyticAt ℂ F (0,0) := d.U_analytic.sub analyticAt_snd
  have haxis : ∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0 := by
    filter_upwards [d.U_axis] with δ hδ
    simp only [F,hδ,sub_zero]
  have ht : Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) :=
    (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
  have hderiv : ∀ᶠδ:ℂ in 𝓝 0,deriv (fun w:ℂ=>F (δ,w)) 0=0 := by
    filter_upwards [d.U_axis_deriv,ht.eventually d.U_analytic.eventually_analyticAt] with δ hD hUδ
    have hDu : HasDerivAt (fun w:ℂ=>d.U (δ,w)) (deriv (fun w:ℂ=>d.U (δ,w)) 0) 0 :=
      hUδ.curry_right.differentiableAt.hasDerivAt
    have hd : HasDerivAt (fun w:ℂ=>F (δ,w)) (0:ℂ) 0 := by
      convert! hDu.sub (hasDerivAt_id (0:ℂ)) using 1
      rw [hD]
      ring
    exact hd.deriv
  exact analytic_parameter_quadratic_bound F hF haxis hderiv
end WP.Analysis
