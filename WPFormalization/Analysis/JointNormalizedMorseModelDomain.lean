import WPFormalization.Analysis.NormalizedMorseModelDomain
/-! A companion to the existing common Morse domain retains the genuinely JOINT holomorphy of every transformed amplitude on the same product domain. It constructs the coordinates and all data from the analytic phase and given amplitude family; the older fiber-domain API is unchanged. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma exists_joint_normalized_morse_model_domain (F a y:ℂ × ℂ→ℂ)
    (hF:AnalyticAt ℂ F (0,0))(ha:AnalyticAt ℂ a (0,0))(hy:AnalyticAt ℂ y (0,0))
    (hjet:∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0 ∧ deriv (fun u:ℂ=>F (δ,u)) 0=0 ∧
      iteratedDeriv 2 (fun u:ℂ=>F (δ,u)) 0=-1)
    (Ω:Set ℂ)(f:ℕ→ℂ→ℂ)(C B:ℝ)(hΩ:IsOpen Ω)(hcover:y (0,0)∈Ω)
    (hC:0<C)(hB:0<B)(hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃ d : NormalizedMorseModelDomain F a y f B,
      ∀ j, AnalyticOnNhd ℂ (morseTransformedAmplitude a y f d.U j)
        (Metric.ball (0 : ℂ) d.rho ×ˢ Metric.ball (0 : ℂ) d.R) := by
  obtain ⟨U, W,hU,hW,hU0,hW0,haxis,hconj,Rq, Cw,hRq,hCw,hclose⟩ := exists_normalized_morse_pair F hF hjet
  obtain ⟨Ra,Da,hRa,hDa,hpre,hpreB⟩ := analytic_composition_product_gevrey_two a y (y (0,0)) ha hy rfl
    Ω hΩ hcover f C B hC hB hf hbound
  let T:ℂ × ℂ→ℂ × ℂ := fun z=>(z.1,U z)
  have hT:AnalyticAt ℂ T (0,0) := analyticAt_fst.prod hU
  have hT0:T (0,0)=(0,0) := by simp[T,hU0]
  let ap:ℂ × ℂ→ℂ := fun z=>a (T z)*sndPartial U z
  let yp:ℂ × ℂ→ℂ := fun z=>y (T z)
  have hap:AnalyticAt ℂ ap (0,0) := (ha.comp_of_eq hT hT0).mul (sndPartial_analytic U (0,0) hU)
  have hyp:AnalyticAt ℂ yp (0,0) := hy.comp_of_eq hT hT0
  have hyp0:yp (0,0)=y (0,0) := by simp[yp,hT0]
  obtain ⟨Rb,D,hRb,hD,hpost,hpostB⟩ := analytic_composition_product_gevrey_two ap yp (y (0,0)) hap hyp hyp0
    Ω hΩ hcover f C B hC hB hf hbound
  have hgood:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),AnalyticAt ℂ U z ∧ AnalyticAt ℂ W z ∧
      U (z.1, W z)=z.2 ∧ F (z.1,U z)=-z.2^2/2 := by
    filter_upwards[hU.eventually_analyticAt,hW.eventually_analyticAt,hconj] with z hu hw hc
    exact ⟨hu,hw,hc.1,hc.2.2.1⟩
  obtain ⟨Rn,hRn,hgoodBall⟩ := Metric.eventually_nhds_iff.mp hgood
  obtain ⟨Rφ,hRφ,hφa⟩ := Metric.eventually_nhds_iff.mp hF.eventually_analyticAt
  obtain ⟨Rax,hRax,hax⟩ := Metric.eventually_nhds_iff.mp haxis
  let S:ℝ := min Ra Rφ/2
  have hS:0<S := half_pos (lt_min hRa hRφ)
  have hSRa:S<Ra := (half_lt_self (lt_min hRa hRφ)).trans_le (min_le_left _ _)
  have hSRφ:S<Rφ := (half_lt_self (lt_min hRa hRφ)).trans_le (min_le_right _ _)
  let R:ℝ := min (Rn/2) (min (Rb/2) (min (Rq/2) (min (S/4) (1/(2*Cw)))))
  have hR:0<R := lt_min (half_pos hRn) (lt_min (half_pos hRb) (lt_min (half_pos hRq) (lt_min (by positivity) (by positivity))))
  have hRRn:R<Rn := (min_le_left _ _).trans_lt (half_lt_self hRn)
  have hRRb:R<Rb := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hRb)
  have hRRq:R<Rq := ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self hRq)
  have hRS:R≤S/4 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hRC:R≤1/(2*Cw) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let ρ:ℝ := min (R/2) (min (S/2) (min (Rax/2) (min (Rq/2) (1/(8*Cw)))))
  have hρ:0<ρ := lt_min (half_pos hR) (lt_min (half_pos hS) (lt_min (half_pos hRax) (lt_min (half_pos hRq) (by positivity))))
  have hρR:ρ≤R/2 := min_le_left _ _
  have hρR':ρ<R := hρR.trans_lt (half_lt_self hR)
  have hρS:ρ<S := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hS)
  have hρAx:ρ<Rax := ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self hRax)
  have hρRq:ρ<Rq := ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).trans_lt (half_lt_self hRq)
  have hρC:ρ≤1/(8*Cw) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpoint(δ u:ℂ)(hδ:‖δ‖<Rn)(hu:‖u‖<Rn):
      AnalyticAt ℂ U (δ,u) ∧ AnalyticAt ℂ W (δ,u) ∧ U (δ, W (δ,u))=u ∧ F (δ,U (δ,u))=-u^2/2 := by
    apply hgoodBall
    change dist (δ,u) (0:ℂ × ℂ)<Rn
    simpa only[dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro hδ hu
  have hUat(δ u:ℂ)(hδ:‖δ‖<ρ)(hu:‖u‖<R):AnalyticAt ℂ U (δ,u) :=
    (hpoint δ u (hδ.trans (hρR'.trans hRRn)) (hu.trans hRRn)).1
  have hWcontrol(δ u:ℂ)(hδ:‖δ‖<ρ)(hu:‖u‖≤ρ):
      ‖W (δ,u)-u‖≤Cw*‖u‖^2 ∧ U (δ, W (δ,u))=u := by
    refine ⟨(hclose δ u (hδ.trans hρRq) (hu.trans_lt hρRq)).2,?_⟩
    exact (hpoint δ u (hδ.trans (hρR'.trans hRRn)) (hu.trans_lt (hρR'.trans hRRn))).2.2.1
  refine ⟨{
    U := U
    W := W
    rho := ρ
    R := R
    S := S
    D := D
    Cw := Cw
    rho_pos := hρ
    R_pos := hR
    S_pos := hS
    D_pos := hD
    Cw_pos := hCw
    rho_R := hρR
    rho_S := hρS
    fibers := ?_
    phase_diff := ?_
    U_diff := ?_
    maps := ?_
    quadratic := ?_
    pre_diff := ?_
    post_diff := ?_
    transform := ?_
    bound := ?_
    W_control := fun δ hδ u hu => hWcontrol δ u hδ hu
    endpoints := ?_ },?_⟩
  · intro δ hδ
    have hp := hpoint δ 0 (hδ.trans (hρR'.trans hRRn)) (by simpa using hRn)
    have haxδ := hax (show dist δ 0<Rax by rw[dist_zero_right];exact hδ.trans hρAx)
    exact ⟨hp.1.curry_right,hp.2.1.curry_right,haxδ.1,haxδ.2.1,haxδ.2.2.1⟩
  · intro δ hδ u hu
    have huS:‖u‖<S := by simpa only[Metric.mem_ball,dist_zero_right] using hu
    have hp:AnalyticAt ℂ F (δ,u) := hφa (by
      change dist (δ,u) (0:ℂ × ℂ)<Rφ
      simpa only[dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro (hδ.trans (hρS.trans hSRφ)) (huS.trans hSRφ))
    exact hp.curry_right.differentiableAt.differentiableWithinAt
  · intro δ hδ u hu
    exact (hUat δ u hδ (by simpa only[Metric.mem_ball,dist_zero_right] using hu)).curry_right.differentiableAt.differentiableWithinAt
  · intro δ hδ u hu
    have huR:‖u‖<R := by simpa only[Metric.mem_ball,dist_zero_right] using hu
    have hc:‖U (δ,u)-u‖≤Cw*‖u‖^2 := (hclose δ u (hδ.trans hρRq) (huR.trans hRRq)).1
    have hCu:Cw*‖u‖≤1/2 := by
      have hh:‖u‖*(2*Cw)≤1 := (le_div_iff₀ (by positivity)).mp (huR.le.trans hRC)
      nlinarith
    have hn:‖U (δ,u)‖≤‖U (δ,u)-u‖+‖u‖ := by simpa only[sub_add_cancel] using norm_add_le (U (δ,u)-u) u
    have hm := mul_le_mul_of_nonneg_right hCu (norm_nonneg u)
    rw[Metric.mem_ball,dist_zero_right]
    nlinarith
  · intro δ hδ u hu
    exact (hpoint δ u (hδ.trans (hρR'.trans hRRn))
      ((show ‖u‖<R from by simpa only[Metric.mem_ball,dist_zero_right] using hu).trans hRRn)).2.2.2
  · intro δ hδ j u hu
    have huS:‖u‖<S := by simpa only[Metric.mem_ball,dist_zero_right] using hu
    have hp:AnalyticAt ℂ (morseSourceAmplitude a y f j) (δ,u) := hpre j _ (by
      simpa only[Metric.mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff] using
        And.intro (hδ.trans (hρS.trans hSRa)) (huS.trans hSRa))
    exact hp.curry_right.differentiableAt.differentiableWithinAt
  · intro δ hδ j u hu
    have huR:‖u‖≤R := by simpa only[Metric.mem_closedBall,dist_zero_right] using hu
    have he:morseTransformedAmplitude a y f U j=(fun z:ℂ × ℂ=>ap z*f j (yp z)) := by
      funext z
      dsimp only[morseTransformedAmplitude,ap,yp,T]
      ring
    have hp:AnalyticAt ℂ (morseTransformedAmplitude a y f U j) (δ,u) := by
      rw[he]
      have hmem : (δ,u) ∈ Metric.ball (0 : ℂ × ℂ) Rb := by
        simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff] using
          And.intro (hδ.trans (hρR'.trans hRRb)) (huR.trans_lt hRRb)
      exact hpost j _ hmem
    exact hp.curry_right.differentiableAt.differentiableWithinAt
  · intro δ hδ j u hu
    have hp := sndPartial_eq_deriv U (δ,u) (hUat δ u hδ (by simpa only[Metric.mem_ball,dist_zero_right] using hu))
    dsimp only[morseSourceAmplitude,morseTransformedAmplitude]
    rw[hp]
  · intro δ hδ j u hu
    have huR:‖u‖≤R := by simpa only[Metric.mem_closedBall,dist_zero_right] using hu
    have he:morseTransformedAmplitude a y f U j (δ,u)=ap (δ,u)*f j (yp (δ,u)) := by
      dsimp only[morseTransformedAmplitude,ap,yp,T]
      ring
    rw[he]
    apply hpostB j
    simpa only [Prod.norm_def, max_lt_iff] using
      And.intro (hδ.trans (hρR'.trans hRRb)) (huR.trans_lt hRRb)
  · intro δ hδ r hr
    have hrR:r≤R/2 := hr.2.trans hρR
    have hp:‖(r:ℂ)‖=r := Complex.norm_of_nonneg hr.1.le
    have hn:‖-(r:ℂ)‖=r := by rw[norm_neg,hp]
    have hquad(z:ℂ)(hz:‖z‖=r):‖W (δ,z)-z‖≤Cw*r^2 := by
      simpa only[hz] using (hWcontrol δ z hδ (hz.le.trans hr.2)).1
    have hquarter(z:ℂ)(hz:‖z‖=r):‖W (δ,z)-z‖≤r/4 := by
      have hmul:r*(8*Cw)≤1 := (le_div_iff₀ (by positivity)).mp (hr.2.trans hρC)
      have hm := mul_le_mul_of_nonneg_right hmul hr.1.le
      exact (hquad z hz).trans (by nlinarith)
    have hinside(z:ℂ)(hz:‖z‖=r):‖W (δ,z)‖<R := by
      have hh:‖W (δ,z)‖≤‖W (δ,z)-z‖+‖z‖ := by simpa only[sub_add_cancel] using norm_add_le (W (δ,z)-z) z
      rw[hz] at hh
      have ht := hquarter z hz
      nlinarith
    have hinv(z:ℂ)(hz:‖z‖=r):U (δ, W (δ,z))=z := (hWcontrol δ z hδ (hz.le.trans hr.2)).2
    exact ⟨hquad _ hp,by simpa only[sub_neg_eq_add] using hquad _ hn,
      hquarter _ hp,by simpa only[sub_neg_eq_add] using hquarter _ hn,
      hinside _ hp,hinside _ hn,hinv _ hp,hinv _ hn⟩
  · intro j z hz
    have hδ : ‖z.1‖ < ρ := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1
    have hu : ‖z.2‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hz.2
    have he : morseTransformedAmplitude a y f U j = (fun z : ℂ × ℂ => ap z * f j (yp z)) := by
      funext z
      dsimp only [morseTransformedAmplitude,ap,yp,T]
      ring
    rw [he]
    apply hpost j
    simpa only [Metric.mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff] using
      And.intro (hδ.trans (hρR'.trans hRRb)) (hu.trans hRRb)
end WP.Analysis
