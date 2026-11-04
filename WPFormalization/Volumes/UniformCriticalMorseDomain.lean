import WPFormalization.Volumes.CriticalGaussianModel
import WPFormalization.Volumes.CriticalModelGrowth
import WPFormalization.Volumes.CriticalMorseForward
/-! Common actual Morse source/target disks and endpoint controls, uniform in the complex critical parameter and every amplitude order. The given coefficient family and its Gevrey base are retained. All inverse identities are restricted to genuine common domains before use. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma CriticalGaussianCoordinateData.uniform_morse_model_domain
    (d:CriticalGaussianCoordinateData) (Q:ℂ→ℂ) (p:ℕ) (f:ℕ→ℂ→ℂ)
    (Ω:Set ℂ) (C B:ℝ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hΩ:IsOpen Ω) (hcover:(y₀:ℂ)∈Ω) (hC:0<C) (hB:0<B)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2) :
    ∃(W:ℂ × ℂ → ℂ)(ρ R S D Cw:ℝ),0<ρ ∧ 0<R ∧ 0<S ∧ 0<D ∧ 0<Cw ∧
      ρ≤R/2 ∧ ρ<S ∧
      ∀δ:ℂ,‖δ‖<ρ→
        DifferentiableOn ℂ (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u)) (Metric.ball 0 S) ∧
        DifferentiableOn ℂ (fun u:ℂ=>d.U (δ,u)) (Metric.ball 0 R) ∧
        MapsTo (fun u:ℂ=>d.U (δ,u)) (Metric.ball 0 R) (Metric.ball 0 S) ∧
        (∀u∈Metric.ball (0:ℂ) R,d.kernel.centeredPhase d.L d.q (δ,d.U (δ,u))=-u^2/2) ∧
        (∀j,DifferentiableOn ℂ (fun u:ℂ=>d.preMorseAmplitude Q p f j (δ,u)) (Metric.ball 0 S)) ∧
        (∀j,DifferentiableOn ℂ (fun u:ℂ=>d.modelAmplitude Q p f j (δ,u)) (Metric.closedBall 0 R)) ∧
        (∀j u,u∈Metric.ball (0:ℂ) R→d.preMorseAmplitude Q p f j (δ,d.U (δ,u))*deriv (fun u:ℂ=>d.U (δ,u)) u=d.modelAmplitude Q p f j (δ,u)) ∧
        (∀j u,u∈Metric.closedBall (0:ℂ) R→‖d.modelAmplitude Q p f j (δ,u)‖≤D*B^j*(j.factorial:ℝ)^2) ∧
        ∀r∈Ioc (0:ℝ) ρ,
          ‖W (δ,(r:ℂ))-(r:ℂ)‖≤Cw*r^2 ∧ ‖W (δ,-(r:ℂ))+(r:ℂ)‖≤Cw*r^2 ∧
          ‖W (δ,(r:ℂ))-(r:ℂ)‖≤r/4 ∧ ‖W (δ,-(r:ℂ))+(r:ℂ)‖≤r/4 ∧
          ‖W (δ,(r:ℂ))‖<R ∧ ‖W (δ,-(r:ℂ))‖<R ∧
          d.U (δ,W (δ,(r:ℂ)))=(r:ℂ) ∧ d.U (δ,W (δ,-(r:ℂ)))= -(r:ℂ) := by
  let A:ℂ × ℂ → ℂ:=d.kernel.jointAmplitude Q p d.q
  let y:ℂ × ℂ → ℂ:=fun z=>(y₀:ℂ)-z.1*d.q z
  have hA:AnalyticAt ℂ A (0,0):=d.kernel.jointAmplitude_analytic Q hQ hQ0 p d.q d.q_analytic d.q_zero
  have hy:AnalyticAt ℂ y (0,0):=analyticAt_const.sub (analyticAt_fst.mul d.q_analytic)
  have hy0:y (0,0)=(y₀:ℂ):=by simp[y]
  obtain ⟨Ra,Da,hRa,hDa,hpre,hpreB⟩:=analytic_composition_product_gevrey_two A y y₀ hA hy hy0 Ω hΩ hcover f C B hC hB hf hbound
  obtain ⟨ha,hy'⟩:=d.modelAmplitude_geometry Q hQ hQ0 p
  let ap:ℂ × ℂ → ℂ:=fun z=>d.kernel.jointAmplitude Q p d.q (z.1,d.U z)*sndPartial d.U z
  let yp:ℂ × ℂ → ℂ:=fun z=>(y₀:ℂ)-z.1*d.q (z.1,d.U z)
  have hyp0:yp (0,0)=(y₀:ℂ):=by simp[yp]
  obtain ⟨Rb,D,hRb,hD,hpost,hpostB⟩:=analytic_composition_product_gevrey_two ap yp y₀ ha hy' hyp0 Ω hΩ hcover f C B hC hB hf hbound
  have hφ:=d.kernel.centeredPhase_analytic d.L d.q d.L_analytic d.q_analytic d.q_zero
  obtain ⟨Rφ,hRφ,hφa⟩:=Metric.eventually_nhds_iff.mp hφ.eventually_analyticAt
  obtain ⟨Rn,hRn,hLa,hqa,hUa,haxis,hfold,hphys⟩:=d.common_neighborhood
  obtain ⟨Ru,Cu,hRu,hCu,hUclose⟩:=d.U_quadratic_bound
  obtain ⟨W,hW,hW0,hWaxis,hWD,hUW,hWU,hphase,Rw,Cw,hRw,hCw,hWclose⟩:=d.exists_forward_morse_coordinate
  obtain ⟨Ri,hRi,hinv⟩:=Metric.eventually_nhds_iff.mp hUW
  let S:ℝ:=min Ra Rφ/2
  have hS:0<S:=half_pos (lt_min hRa hRφ)
  have hSRa:S<Ra:=(half_lt_self (lt_min hRa hRφ)).trans_le (min_le_left _ _)
  have hSRφ:S<Rφ:=(half_lt_self (lt_min hRa hRφ)).trans_le (min_le_right _ _)
  let R:ℝ:=min (Rn/2) (min (Rb/2) (min (Ru/2) (min (S/4) (1/(2*Cu)))))
  have hR:0<R:=lt_min (half_pos hRn) (lt_min (half_pos hRb) (lt_min (half_pos hRu) (lt_min (by positivity) (by positivity))))
  have hRRn:R<Rn:=(min_le_left _ _).trans_lt (half_lt_self hRn)
  have hRRb:R<Rb:=((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hRb)
  have hRRu:R<Ru:=((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self hRu)
  have hRS:R≤S/4:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hRC:R≤1/(2*Cu):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let ρ:ℝ:=min (R/2) (min (S/2) (min (Ri/2) (min (Rw/2) (1/(8*Cw)))))
  have hρ:0<ρ:=lt_min (half_pos hR) (lt_min (half_pos hS) (lt_min (half_pos hRi) (lt_min (half_pos hRw) (by positivity))))
  have hρR:ρ≤R/2:=min_le_left _ _
  have hρR':ρ<R:=hρR.trans_lt (half_lt_self hR)
  have hρS:ρ<S:=((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hS)
  have hρRi:ρ<Ri:=((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self hRi)
  have hρRw:ρ<Rw:=((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).trans_lt (half_lt_self hRw)
  have hρC:ρ≤1/(8*Cw):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨W,ρ,R,S,D,Cw,hρ,hR,hS,hD,hCw,hρR,hρS,?_⟩
  intro δ hδ
  have hδR:‖δ‖<R:=hδ.trans hρR'
  have hδn:‖δ‖<Rn:=hδR.trans hRRn
  have hδu:‖δ‖<Ru:=hδR.trans hRRu
  have hδw:‖δ‖<Rw:=hδ.trans hρRw
  have hδi:‖δ‖<Ri:=hδ.trans hρRi
  have hδS:‖δ‖<S:=hδ.trans hρS
  have hUat(u:ℂ)(hu:‖u‖<R):AnalyticAt ℂ d.U (δ,u):=hUa _ ⟨by simpa only[Metric.mem_ball,dist_zero_right] using hδn,by simpa only[Metric.mem_ball,dist_zero_right] using hu.trans hRRn⟩
  have hUm:MapsTo (fun u:ℂ=>d.U (δ,u)) (Metric.ball 0 R) (Metric.ball 0 S) := by
    intro u hu
    have huR:‖u‖<R:=by simpa only[Metric.mem_ball,dist_zero_right] using hu
    have hc:=hUclose δ u hδu (huR.trans hRRu)
    have hCu:Cu*‖u‖≤1/2 := by
      have hh:‖u‖*(2*Cu)≤1:=(le_div_iff₀ (by positivity)).mp (huR.le.trans hRC)
      nlinarith
    have hn:‖d.U (δ,u)‖≤‖d.U (δ,u)-u‖+‖u‖:=by simpa only[sub_add_cancel] using norm_add_le (d.U (δ,u)-u) u
    have hmul:=mul_le_mul_of_nonneg_right hCu (norm_nonneg u)
    rw[Metric.mem_ball,dist_zero_right]
    nlinarith
  refine ⟨?_,?_,hUm,?_,?_,?_,?_,?_,?_⟩
  · intro u hu
    have huS:‖u‖<S:=by simpa only[Metric.mem_ball,dist_zero_right] using hu
    have hp:AnalyticAt ℂ (d.kernel.centeredPhase d.L d.q) (δ,u):=hφa (by change dist (δ,u) (0:ℂ × ℂ)<Rφ;simpa only[dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro (hδS.trans hSRφ) (huS.trans hSRφ))
    exact hp.curry_right.differentiableAt.differentiableWithinAt
  · intro u hu
    exact (hUat u (by simpa only[Metric.mem_ball,dist_zero_right] using hu)).curry_right.differentiableAt.differentiableWithinAt
  · intro u hu
    exact (hfold δ u hδn ((show ‖u‖<R from by simpa only[Metric.mem_ball,dist_zero_right] using hu).trans hRRn)).2
  · intro j u hu
    have huS:‖u‖<S:=by simpa only[Metric.mem_ball,dist_zero_right] using hu
    have hp:AnalyticAt ℂ (d.preMorseAmplitude Q p f j) (δ,u):=hpre j _ (by simpa only[Metric.mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro (hδS.trans hSRa) (huS.trans hSRa))
    exact hp.curry_right.differentiableAt.differentiableWithinAt
  · intro j u hu
    have huR:‖u‖≤R:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hu
    have hp:AnalyticAt ℂ (d.modelAmplitude Q p f j) (δ,u) := by
      have he:(fun z:ℂ × ℂ=>ap z*f j (yp z))=d.modelAmplitude Q p f j := by
        funext z
        dsimp only[ap,yp,CriticalGaussianCoordinateData.modelAmplitude]
        ring
      rw[←he]
      exact hpost j _ (by simpa only[Metric.mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro (hδR.trans hRRb) (huR.trans_lt hRRb))
    exact hp.curry_right.differentiableAt.differentiableWithinAt
  · intro j u hu
    have hp:=sndPartial_eq_deriv d.U (δ,u) (hUat u (by simpa only[Metric.mem_ball,dist_zero_right] using hu))
    dsimp only[CriticalGaussianCoordinateData.preMorseAmplitude,CriticalGaussianCoordinateData.modelAmplitude]
    rw[hp]
  · intro j u hu
    have huR:‖u‖≤R:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hu
    have he:d.modelAmplitude Q p f j (δ,u)=ap (δ,u)*f j (yp (δ,u)):=by
      dsimp only[ap,yp,CriticalGaussianCoordinateData.modelAmplitude]
      ring
    rw[he]
    exact hpostB j _ (by simpa only[Prod.norm_def,max_lt_iff] using And.intro (hδR.trans hRRb) (huR.trans_lt hRRb))
  · intro r hr
    have hrR:r≤R/2:=hr.2.trans hρR
    have hrw:r<Rw:=hr.2.trans_lt hρRw
    have hri:r<Ri:=hr.2.trans_lt hρRi
    have hrc:r≤1/(8*Cw):=hr.2.trans hρC
    have hp:‖(r:ℂ)‖=r:=Complex.norm_of_nonneg hr.1.le
    have hn:‖-(r:ℂ)‖=r:=by rw[norm_neg,hp]
    have hquadratic(z:ℂ)(hz:‖z‖=r):‖W (δ,z)-z‖≤Cw*r^2:=by
      simpa only[hz] using hWclose δ z hδw (hz.trans_lt hrw)
    have hquarter(z:ℂ)(hz:‖z‖=r):‖W (δ,z)-z‖≤r/4:=by
      have hmul: r*(8*Cw)≤1:=(le_div_iff₀ (by positivity)).mp hrc
      have hm:=mul_le_mul_of_nonneg_right hmul hr.1.le
      exact (hquadratic z hz).trans (by nlinarith)
    have hinside(z:ℂ)(hz:‖z‖=r):‖W (δ,z)‖<R := by
      have hh:‖W (δ,z)‖≤‖W (δ,z)-z‖+‖z‖:=by simpa only[sub_add_cancel] using norm_add_le (W (δ,z)-z) z
      rw[hz] at hh
      have ht:=hquarter z hz
      nlinarith
    have hinverse(z:ℂ)(hz:‖z‖=r):d.U (δ,W (δ,z))=z:=
      hinv (by change dist (δ,z) (0:ℂ × ℂ)<Ri;simpa only[dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro hδi (hz.trans_lt hri))
    exact ⟨hquadratic _ hp,by simpa only[sub_neg_eq_add] using hquadratic _ hn,
      hquarter _ hp,by simpa only[sub_neg_eq_add] using hquarter _ hn,
      hinside _ hp,hinside _ hn,hinverse _ hp,hinverse _ hn⟩
end WP.Analysis
