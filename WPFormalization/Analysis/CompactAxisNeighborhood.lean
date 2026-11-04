import WPFormalization.Analysis.ParameterHadamard
import Mathlib.Topology.Compactness.Compact
/-! Compactness gives a single complex parameter neighborhood and a single transverse disk from genuine local data. The phase and all Gevrey amplitudes retain their common radius before every order. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma compact_axis_uniform_neighborhood (K:Set ℂ) (hK:IsCompact K) (P:ℂ × ℂ → Prop)
    (hP:∀x ∈ K,∀ᶠz:ℂ × ℂ in 𝓝 (x,0),P z) :
    ∃Ω:Set ℂ,IsOpen Ω ∧ K⊆Ω ∧ ∃r:ℝ,0<r ∧ ∀x ∈ Ω,∀u:ℂ,‖u‖<r → P (x,u) := by
  let O:Set (ℂ × ℂ):=interior {z|P z}
  have hsub:K ×ˢ {(0:ℂ)}⊆O := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    have hz:u=0 := by simpa only[mem_singleton_iff] using hu
    subst u
    exact mem_interior_iff_mem_nhds.mpr (hP x hx)
  obtain ⟨Ω,V,hΩ,hV,hKΩ,h0V,hprod⟩:=generalized_tube_lemma hK isCompact_singleton isOpen_interior hsub
  have hV0:(0:ℂ) ∈ V:=h0V (by simp)
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hV 0 hV0
  refine ⟨Ω,hΩ,hKΩ,r,hr,?_⟩
  intro x hx u hu
  have huv:u ∈ V:=hball (by simpa only[Metric.mem_ball,dist_zero_right] using hu)
  exact interior_subset (hprod ⟨hx,huv⟩)

lemma normalized_phase_local_square_bound (F:ℂ × ℂ → ℂ)
    (hF:AnalyticAt ℂ F (0,0))
    (haxis:∀ᶠz:ℂ in 𝓝 0,F (z,0)=0)
    (hD:∀ᶠz:ℂ in 𝓝 0,deriv (fun u:ℂ=>F (z,u)) 0=0)
    (hsecond:iteratedDeriv 2 (fun u:ℂ=>F (0,u)) 0=-1):
    ∀ᶠz:ℂ × ℂ in 𝓝 (0,0),AnalyticAt ℂ F z ∧ ‖F z‖ ≤ ‖z.2‖^2 := by
  obtain ⟨G,hG,hG0,hfac⟩:=exists_analytic_parameter_square_factor_with_value F hF haxis hD
  have hGv:G (0,0)=-(1/2:ℂ) := by
    change G 0=-(1/2:ℂ)
    rw[hG0,hsecond]
    ring
  have hnorm0:‖G (0,0)‖<(1:ℝ) := by rw[hGv];norm_num
  have hnorm:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),‖G z‖<1:=
    hG.continuousAt.norm.tendsto.eventually (eventually_lt_nhds hnorm0)
  filter_upwards[hfac,hnorm,hF.eventually_analyticAt] with z hz hn ha
  refine ⟨ha,?_⟩
  rw[hz,norm_mul,norm_pow]
  nlinarith [sq_nonneg ‖z.2‖]

lemma compact_normalized_phase_quadratic_bound (K:Set ℂ) (hK:IsCompact K) (F:ℂ × ℂ → ℂ)
    (hF:∀x ∈ K,AnalyticAt ℂ F (x,0))
    (hjet:∀x ∈ K,∀ᶠq:ℂ in 𝓝 x,F (q,0)=0 ∧ deriv (fun u:ℂ=>F (q,u)) 0=0 ∧
      iteratedDeriv 2 (fun u:ℂ=>F (q,u)) 0=-1) :
    ∃Ω:Set ℂ,IsOpen Ω ∧ K⊆Ω ∧ ∃r:ℝ,0<r ∧ ∀x ∈ Ω,∀u:ℂ,‖u‖<r →
      AnalyticAt ℂ F (x,u) ∧ ‖F (x,u)‖ ≤ ‖u‖^2 := by
  apply compact_axis_uniform_neighborhood K hK (fun z=>AnalyticAt ℂ F z ∧ ‖F z‖ ≤ ‖z.2‖^2)
  intro x hx
  let G:ℂ × ℂ → ℂ:=fun z=>F (x+z.1,z.2)
  have hm:AnalyticAt ℂ (fun z:ℂ × ℂ=>(x+z.1,z.2)) (0,0) :=
    (analyticAt_const.add analyticAt_fst).prod analyticAt_snd
  have hG:AnalyticAt ℂ G (0,0) := (hF x hx).comp_of_eq hm (by simp)
  have ht:Tendsto (fun q:ℂ=>x+q) (𝓝 0) (𝓝 x) := by
    simpa only[add_zero] using (show ContinuousAt (fun q:ℂ=>x+q) 0 by fun_prop).tendsto
  have hj:∀ᶠq:ℂ in 𝓝 0,G (q,0)=0 ∧ deriv (fun u:ℂ=>G (q,u)) 0=0 ∧
      iteratedDeriv 2 (fun u:ℂ=>G (q,u)) 0=-1 := ht.eventually (hjet x hx)
  have hb:=normalized_phase_local_square_bound G hG (hj.mono (fun q hq=>hq.1))
    (hj.mono (fun q hq=>hq.2.1)) hj.self_of_nhds.2.2
  have hp:Tendsto (fun z:ℂ × ℂ=>(z.1-x,z.2)) (𝓝 (x,0)) (𝓝 ((0,0):ℂ × ℂ)) := by
    have hc:ContinuousAt (fun z:ℂ × ℂ=>(z.1-x,z.2)) (x,0) := by fun_prop
    simpa only[sub_self] using hc.tendsto
  filter_upwards [hp.eventually hb,(hF x hx).eventually_analyticAt] with z hz ha
  refine ⟨ha,?_⟩
  have he:x+(z.1-x)=z.1 := by ring
  simpa only[G,he,Prod.mk.eta] using hz.2
lemma compact_axis_composition_gevrey_two_family (K:Set ℂ) (hK:IsCompact K)
    (a y:ℂ × ℂ → ℂ) (Ω:Set ℂ) (hΩ:IsOpen Ω) (f:ℕ → ℂ → ℂ) (C B:ℝ)
    (_hC:0 ≤ C) (_hB:0 ≤ B)
    (ha:∀x ∈ K,AnalyticAt ℂ a (x,0)) (hy:∀x ∈ K,AnalyticAt ℂ y (x,0))
    (ha0:∀x ∈ K,a (x,0)=1) (hy0:∀x ∈ K,y (x,0) ∈ Ω)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hbound:∀j z,z ∈ Ω → ‖f j z‖ ≤ C*B^j*(j.factorial:ℝ)^2):
    ∃U:Set ℂ,IsOpen U ∧ K⊆U ∧ ∃r:ℝ,0<r ∧
      (∀j,AnalyticOnNhd ℂ (fun p:ℂ × ℂ=>a p*f j (y p)) (U ×ˢ Metric.ball 0 r)) ∧
      ∀j x,x ∈ U → ∀u:ℂ,‖u‖<r → ‖a (x,u)*f j (y (x,u))‖ ≤ 2*C*B^j*(j.factorial:ℝ)^2 := by
  have hloc(x:ℂ)(hx:x ∈ K):∀ᶠz:ℂ × ℂ in 𝓝 (x,0),
      AnalyticAt ℂ a z ∧ AnalyticAt ℂ y z ∧ y z ∈ Ω ∧ ‖a z‖ ≤ 2 := by
    have hnorm0:‖a (x,0)‖<(2:ℝ):=by rw[ha0 x hx];norm_num
    have hab:∀ᶠz:ℂ × ℂ in 𝓝 (x,0),‖a z‖<2:=
      (ha x hx).continuousAt.norm.tendsto.eventually (eventually_lt_nhds hnorm0)
    have hym:∀ᶠz:ℂ × ℂ in 𝓝 (x,0),y z ∈ Ω:=
      (hy x hx).continuousAt.eventually (hΩ.mem_nhds (hy0 x hx))
    filter_upwards[(ha x hx).eventually_analyticAt,(hy x hx).eventually_analyticAt,hym,hab]
      with z h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4.le⟩
  obtain ⟨U,hU,hKU,r,hr,hprop⟩:=compact_axis_uniform_neighborhood K hK
    (fun z=>AnalyticAt ℂ a z ∧ AnalyticAt ℂ y z ∧ y z ∈ Ω ∧ ‖a z‖ ≤ 2) hloc
  refine ⟨U,hU,hKU,r,hr,?_,?_⟩
  · intro j z hz
    have ht:=hprop z.1 hz.1 z.2 (by simpa only[Metric.mem_ball,dist_zero_right] using hz.2)
    exact ht.1.mul ((hf j (y z) ht.2.2.1).comp (f:=y) ht.2.1)
  · intro j x hx u hu
    have ht:=hprop x hx u hu
    rw[norm_mul]
    calc _ ≤ 2*(C*B^j*(j.factorial:ℝ)^2) :=
          mul_le_mul ht.2.2.2 (hbound j (y (x,u)) ht.2.2.1) (norm_nonneg _) (by norm_num)
         _ = _ := by ring
end WP.Analysis
