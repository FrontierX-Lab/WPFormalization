import WPFormalization.Analysis.FixedMorseIntegral
import WPFormalization.Analysis.NormalizedMorseFamily
import WPFormalization.Analysis.CoefficientSubstitution
/-! Proved finite analytic amplitude bounds and genuine Morse model comparison. The holomorphic domains, endpoint controls and common bounds are constructed from the actual analytic germs, uniformly for every smaller cutoff. No contour or stationary-phase estimate is assumed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma finite_analytic_family_common_circle (f:ℕ→ℂ→ℂ) (N:ℕ)
    (hf:∀s≤N,AnalyticAt ℂ (f s) 0) :
    ∃R C:ℝ,0<R ∧ 0<C ∧ ∀s≤N,
      DifferentiableOn ℂ (f s) (Metric.closedBall 0 R) ∧
      ∀z∈Metric.closedBall (0:ℂ) R,‖f s z‖≤C := by
  let C:ℝ:=(∑s∈Finset.range (N+1),‖f s 0‖)+1
  have hC:0<C:=by dsimp[C];positivity
  have hC0(s:ℕ)(hs:s∈Finset.range (N+1)):‖f s 0‖<C := by
    have hb:=Finset.single_le_sum (f:=fun s:ℕ=>‖f s 0‖) (fun s hs=>norm_nonneg _) hs
    dsimp only[C]
    linarith
  have hnear:∀ᶠz:ℂ in 𝓝 0,∀s∈Finset.range (N+1),AnalyticAt ℂ (f s) z ∧ ‖f s z‖≤C := by
    apply (Finset.eventually_all _).mpr
    intro s hs
    have hfs:=hf s (by have hh:=Finset.mem_range.mp hs;omega)
    filter_upwards[hfs.eventually_analyticAt,hfs.continuousAt.norm.tendsto.eventually
      (eventually_lt_nhds (hC0 s hs))] with z hz hb
    exact ⟨hz,hb.le⟩
  obtain ⟨ρ,hρ,hball⟩:=Metric.eventually_nhds_iff.mp hnear
  let R:ℝ:=ρ/2
  have hR:0<R:=half_pos hρ
  have hRp:R<ρ:=by dsimp[R];linarith
  refine ⟨R,C,hR,hC,?_⟩
  intro s hs
  have hp(z:ℂ)(hz:z∈Metric.closedBall (0:ℂ) R):AnalyticAt ℂ (f s) z ∧ ‖f s z‖≤C :=
    hball (by have hh:‖z‖≤R:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
              simpa only[dist_zero_right] using hh.trans_lt hRp) s (Finset.mem_range.mpr (by omega))
  exact ⟨fun z hz=>(hp z hz).1.differentiableAt.differentiableWithinAt,fun z hz=>(hp z hz).2⟩
end WP.Analysis

namespace WP.Analysis
lemma fixed_morse_finite_amplitude_cut_data_all_radii (φ U W:ℂ→ℂ) (a:ℕ→ℂ→ℂ) (N:ℕ)
    (hφ:AnalyticAt ℂ φ 0) (hU:AnalyticAt ℂ U 0) (hW:AnalyticAt ℂ W 0) (hU0:U 0=0)
    (ha:∀s≤N,AnalyticAt ℂ (a s) 0)
    (hconj:∀ᶠz:ℂ in 𝓝 0,U (W z)=z ∧ φ (U z)=-z^2/2)
    (ρ C:ℝ) (hρ:0<ρ) (hC:0<C)
    (hclose:∀z:ℂ,‖z‖<ρ→‖W z-z‖≤C*‖z‖^2) :
    ∃r R S M:ℝ,0<r ∧ r≤R/2 ∧ r<S ∧ 0<M ∧
      DifferentiableOn ℂ φ (Metric.ball 0 S) ∧
      DifferentiableOn ℂ U (Metric.ball 0 R) ∧
      MapsTo U (Metric.ball 0 R) (Metric.ball 0 S) ∧
      (∀z∈Metric.ball (0:ℂ) R,φ (U z)=-z^2/2) ∧
      (∀s≤N,DifferentiableOn ℂ (a s) (Metric.ball 0 S) ∧
        ∀z∈Metric.ball (0:ℂ) R,‖a s (U z)*deriv U z‖≤M) ∧
      ∀r'∈Ioc (0:ℝ) r,‖W (r':ℂ)-(r':ℂ)‖≤r'/4 ∧ ‖W (-(r':ℂ))+(r':ℂ)‖≤r'/4 ∧
        ‖W (r':ℂ)‖<R ∧ ‖W (-(r':ℂ))‖<R ∧
        U (W (r':ℂ))=(r':ℂ) ∧ U (W (-(r':ℂ)))= -(r':ℂ) := by
  obtain ⟨Ra,Ma,hRa,hMa,hamp⟩:=finite_analytic_family_common_circle a N ha
  have hφa:∀ᶠz:ℂ in 𝓝 0,AnalyticAt ℂ φ z:=hφ.eventually_analyticAt
  obtain ⟨Rp,hRp,hphiball⟩:=Metric.eventually_nhds_iff.mp hφa
  let S:ℝ:=min Ra Rp/2
  have hS:0<S:=half_pos (lt_min hRa hRp)
  have hSRa:S<Ra:= (half_lt_self (lt_min hRa hRp)).trans_le (min_le_left _ _)
  have hSRp:S<Rp:= (half_lt_self (lt_min hRa hRp)).trans_le (min_le_right _ _)
  have hphid:DifferentiableOn ℂ φ (Metric.ball 0 S) := by
    intro z hz
    exact (hphiball (by simpa only[dist_zero_right] using
      (show ‖z‖<S from by simpa only[Metric.mem_ball,dist_zero_right] using hz).trans hSRp)).differentiableAt.differentiableWithinAt
  let b:ℕ→ℂ→ℂ:=fun s z=>a s (U z)*deriv U z
  have hb(s:ℕ)(hs:s≤N):AnalyticAt ℂ (b s) 0 :=
    ((ha s hs).comp_of_eq hU hU0).mul hU.deriv
  obtain ⟨Rb,M,hRb,hM,hpost⟩:=finite_analytic_family_common_circle b N hb
  have hnear:∀ᶠz:ℂ in 𝓝 0,AnalyticAt ℂ U z ∧ U z∈Metric.ball 0 S ∧ φ (U z)=-z^2/2 := by
    have hmap:∀ᶠz:ℂ in 𝓝 0,U z∈Metric.ball 0 S :=
      hU.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (by simpa only[hU0] using Metric.mem_ball_self hS))
    filter_upwards[hU.eventually_analyticAt,hmap,hconj] with z hu hz he
    exact ⟨hu,hz,he.2⟩
  obtain ⟨R0,hR0,hball⟩:=Metric.eventually_nhds_iff.mp hnear
  let R:ℝ:=min R0 Rb/2
  have hR:0<R:=half_pos (lt_min hR0 hRb)
  have hRR0:R<R0:=(half_lt_self (lt_min hR0 hRb)).trans_le (min_le_left _ _)
  have hRRb:R<Rb:=(half_lt_self (lt_min hR0 hRb)).trans_le (min_le_right _ _)
  have hRprop(z:ℂ)(hz:z∈Metric.ball (0:ℂ) R):AnalyticAt ℂ U z ∧ U z∈Metric.ball 0 S ∧ φ (U z)=-z^2/2 :=
    hball (by simpa only[dist_zero_right] using
      (show ‖z‖<R from by simpa only[Metric.mem_ball,dist_zero_right] using hz).trans hRR0)
  obtain ⟨κ,hκ,hend⟩:=Metric.eventually_nhds_iff.mp hconj
  let m:ℝ:=min S (min R (min ρ (min κ (1/(4*C)))))
  have hm:0< m:=lt_min hS (lt_min hR (lt_min hρ (lt_min hκ (by positivity))))
  let r:ℝ:=m/2
  have hr:0<r:=half_pos hm
  have hrm:r< m:=half_lt_self hm
  have hrS:r<S:=hrm.trans_le (min_le_left _ _)
  have hrR:r<R:=hrm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrρ:r<ρ:=hrm.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrκ:r<κ:=hrm.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hrC:r<1/(4*C):=hrm.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hrhalf:r≤R/2:=by
    dsimp only[r]
    exact div_le_div_of_nonneg_right
      ((min_le_right S (min R (min ρ (min κ (1/(4*C)))))).trans (min_le_left _ _)) (by norm_num)
  have hendpoint(r':ℝ)(hr':r'∈Ioc (0:ℝ) r):
      ‖W (r':ℂ)-(r':ℂ)‖≤r'/4 ∧ ‖W (-(r':ℂ))+(r':ℂ)‖≤r'/4 ∧
        ‖W (r':ℂ)‖<R ∧ ‖W (-(r':ℂ))‖<R ∧
        U (W (r':ℂ))=(r':ℂ) ∧ U (W (-(r':ℂ)))= -(r':ℂ) := by
    have hrpρ:r'<ρ:=hr'.2.trans_lt hrρ
    have hrpκ:r'<κ:=hr'.2.trans_lt hrκ
    have hrpC:r'<1/(4*C):=hr'.2.trans_lt hrC
    have hrphalf:r'≤R/2:=hr'.2.trans hrhalf
    have he(z:ℂ)(hz:‖z‖=r'):‖W z-z‖≤r'/4 := by
      have hc:=hclose z (hz.trans_lt hrpρ)
      rw[hz] at hc
      apply hc.trans
      have hh:r'*(4*C)≤1:=(lt_div_iff₀ (by positivity)).mp hrpC |>.le
      have hh':=mul_le_mul_of_nonneg_right hh hr'.1.le
      nlinarith
    have hpos:‖(r':ℂ)‖=r':=Complex.norm_of_nonneg hr'.1.le
    have hneg:‖-(r':ℂ)‖=r':=by rw[norm_neg,hpos]
    have hp:=he (r':ℂ) hpos
    have hn:=he (-(r':ℂ)) hneg
    have hn':‖W (-(r':ℂ))+(r':ℂ)‖≤r'/4:=by simpa only[sub_neg_eq_add] using hn
    have hWball(z:ℂ)(hz:‖z‖=r'):‖W z‖<R := by
      have ht:‖W z‖≤‖W z-z‖+‖z‖:=by simpa only[sub_add_cancel] using norm_add_le (W z-z) z
      rw[hz] at ht
      have hb:=he z hz
      nlinarith
    exact ⟨hp,hn',hWball _ hpos,hWball _ hneg,
      (hend (by simpa only[dist_zero_right,hpos] using hrpκ)).1,
      (hend (by simpa only[dist_zero_right,hneg] using hrpκ)).1⟩
  refine ⟨r,R,S,M,hr,hrhalf,hrS,hM,hphid,(fun z hz=>(hRprop z hz).1.differentiableAt.differentiableWithinAt),
    (fun z hz=>(hRprop z hz).2.1),(fun z hz=>(hRprop z hz).2.2),?_,hendpoint⟩
  · intro s hs
    constructor
    · exact (hamp s hs).1.mono (fun z hz=>Metric.mem_closedBall.mpr (by
        have hzS:‖z‖<S:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
        simpa only[dist_zero_right] using (hzS.trans hSRa).le))
    · intro z hz
      exact (hpost s hs).2 z (Metric.mem_closedBall.mpr (by
        have hzR:‖z‖<R:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
        simpa only[dist_zero_right] using (hzR.trans hRRb).le))
end WP.Analysis

namespace WP.Analysis
lemma fixed_morse_finite_amplitude_integral_comparison (φ U W:ℂ→ℂ) (a:ℕ→ℂ→ℂ) (N:ℕ)
    (hφ:AnalyticAt ℂ φ 0) (hU:AnalyticAt ℂ U 0) (hW:AnalyticAt ℂ W 0) (hU0:U 0=0)
    (ha:∀s≤N,AnalyticAt ℂ (a s) 0)
    (hconj:∀ᶠz:ℂ in 𝓝 0,U (W z)=z ∧ φ (U z)=-z^2/2)
    (ρ C:ℝ) (hρ:0<ρ) (hC:0<C)
    (hclose:∀z:ℂ,‖z‖<ρ→‖W z-z‖≤C*‖z‖^2) :
    ∃r0:ℝ,0<r0 ∧ ∀r∈Ioc (0:ℝ) r0,∃D ε:ℝ,0<D ∧ 0<ε ∧ ∀h:ℝ,1≤h→
      ‖(∑s∈Finset.range (N+1),(∫u:ℝ in (-r)..r,Complex.exp ((h:ℂ)*φ (u:ℂ))*a s (u:ℂ))/(h:ℂ)^s)-
        (∑s∈Finset.range (N+1),(∫w:ℝ in (-r)..r,Complex.exp (-(h:ℂ)/2*(w:ℂ)^2)*
          (a s (U (w:ℂ))*deriv U (w:ℂ)))/(h:ℂ)^s)‖≤D*Real.exp (-(ε*h)) := by
  obtain ⟨r0,R,S,M,hr0,hr0R,hr0S,hM,hφd,hUd,hmap,hphase,hamp,hend⟩:=
    fixed_morse_finite_amplitude_cut_data_all_radii φ U W a N hφ hU hW hU0 ha hconj ρ C hρ hC hclose
  refine ⟨r0,hr0,?_⟩
  intro r hr
  have hrpos:0<r:=hr.1
  have hrR:r<R:=hr.2.trans_lt (by linarith)
  have hrS:r<S:=hr.2.trans_lt hr0S
  obtain ⟨hep,hen,hp,hn,hUp,hUn⟩:=hend r hr
  let ep:ℂ:=W (r:ℂ)-(r:ℂ)
  let en:ℂ:=W (-(r:ℂ))+(r:ℂ)
  have hc:-(r:ℂ)+en=W (-(r:ℂ)):=by dsimp[en];ring
  let D:ℝ:=(N+1:ℕ)*M*r+1
  let ε:ℝ:=r^2/4
  have hD:0<D:=by dsimp[D];positivity
  have hε:0<ε:=by dsimp[ε];positivity
  refine ⟨D,ε,hD,hε,?_⟩
  intro h hh1
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hb(s:ℕ)(hs:s≤N):
      ‖(∫u:ℝ in (-r)..r,Complex.exp ((h:ℂ)*φ (u:ℂ))*a s (u:ℂ))-
        (∫w:ℝ in (-r)..r,Complex.exp (-(h:ℂ)/2*(w:ℂ)^2)*(a s (U (w:ℂ))*deriv U (w:ℂ)))‖≤
        M*Real.exp (-(h/4)*r^2)*(r/2) := by
    have hb0:=fixed_morse_integral_connector_bound φ (a s) U
      (fun z:ℂ=>a s (U z)*deriv U z) h M r R S ep en hh hM.le hr.1 hrR hrS hφd (hamp s hs).1 hUd hmap
      (fun z hz=>⟨hphase z hz,rfl⟩) (hamp s hs).2 hep hen
      (by simpa only[ep,add_sub_cancel] using hp)
      (by rw[hc];exact hn)
      (by simpa only[ep,add_sub_cancel] using hUp)
      (by rw[hc];exact hUn)
    apply hb0.trans
    exact mul_le_mul_of_nonneg_left (by dsimp only[ep,en];linarith) (by positivity)
  rw[←Finset.sum_sub_distrib]
  calc _ ≤ ∑s∈Finset.range (N+1),‖(∫u:ℝ in (-r)..r,Complex.exp ((h:ℂ)*φ (u:ℂ))*a s (u:ℂ))/(h:ℂ)^s-
      (∫w:ℝ in (-r)..r,Complex.exp (-(h:ℂ)/2*(w:ℂ)^2)*(a s (U (w:ℂ))*deriv U (w:ℂ)))/(h:ℂ)^s‖ := norm_sum_le _ _
       _ ≤ ∑s∈Finset.range (N+1),M*Real.exp (-(h/4)*r^2)*(r/2) := by
         apply Finset.sum_le_sum
         intro s hs
         rw[←sub_div,norm_div,norm_pow,Complex.norm_of_nonneg hh.le]
         apply (div_le_div_of_nonneg_right (hb s (Nat.le_of_lt_succ (Finset.mem_range.mp hs))) (pow_nonneg hh.le _)).trans
         apply div_le_self (by positivity)
         exact one_le_pow₀ hh1
       _ = (N+1:ℕ)*(M*Real.exp (-(h/4)*r^2)*(r/2)):=by simp
       _ ≤ D*Real.exp (-(ε*h)) := by
         have he:-(h/4)*r^2= -(ε*h):=by dsimp[ε];ring
         rw[he]
         dsimp only[D]
         have hbase:0≤(N+1:ℕ)*M*r:=by positivity
         nlinarith[Real.exp_pos (-(ε*h))]
end WP.Analysis
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma exists_stationary_morse_germs (β:ℂ→ℂ) (hβ:AnalyticAt ℂ β 0) (hβ0:β 0=0) :
    ∃U W:ℂ→ℂ,AnalyticAt ℂ U 0 ∧ AnalyticAt ℂ W 0 ∧ U 0=0 ∧ W 0=0 ∧
      deriv U 0=1 ∧ deriv W 0=1 ∧
      (∀ᶠz:ℂ in 𝓝 0,U (W z)=z ∧ W (U z)=z ∧
        (U z)^2*(β (U z)-(1/2:ℂ))=-z^2/2) ∧
      ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀z:ℂ,‖z‖<ρ→
        ‖U z-z‖≤C*‖z‖^2 ∧ ‖W z-z‖≤C*‖z‖^2 := by
  let φ:ℂ→ℂ:=fun u=>u^2*(β u-(1/2:ℂ))
  have hφ:AnalyticAt ℂ φ 0 :=(analyticAt_id.pow 2).mul (hβ.sub analyticAt_const)
  have hc(n:ℕ):WP.coeff φ n=if 2≤n then WP.coeff (fun u:ℂ=>β u-(1/2:ℂ)) (n-2) else 0 :=
    coeff_id_pow_mul _ (hβ.sub analyticAt_const) 2 n
  have hφ0:φ 0=0:=by simp[φ]
  have hφ1:deriv φ 0=0:=by simpa[WP.coeff] using hc 1
  have hφ2:iteratedDeriv 2 φ 0=-1 := by
    have he:=hc 2
    norm_num only[Nat.reduceLeDiff,ite_true,Nat.sub_self,WP.coeff,Nat.factorial_zero,Nat.cast_one,
      iteratedDeriv_zero,div_one,hβ0,zero_sub,Nat.factorial_two,Nat.cast_ofNat] at he
    linear_combination 2*he
  let F:ℂ × ℂ→ℂ:=fun v=>φ v.2
  have hF:AnalyticAt ℂ F (0,0):=by
    change AnalyticAt ℂ (fun v:ℂ × ℂ=>φ v.2) (0,0)
    exact AnalyticAt.comp (f:=fun v:ℂ × ℂ=>v.2) (x:=((0,0):ℂ × ℂ)) hφ analyticAt_snd
  have hjet:∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0 ∧ deriv (fun u:ℂ=>F (δ,u)) 0=0 ∧
      iteratedDeriv 2 (fun u:ℂ=>F (δ,u)) 0=-1 :=
    Filter.Eventually.of_forall (fun δ=>⟨hφ0,hφ1,hφ2⟩)
  obtain ⟨U,W,hU,hW,hU0,hW0,haxis,hprops,ρ,C,hρ,hC,hclose⟩:=exists_normalized_morse_pair F hF hjet
  have hline:Tendsto (fun z:ℂ=>((0:ℂ),z)) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) := by
    exact (continuous_const.prodMk continuous_id).continuousAt.tendsto
  refine ⟨(fun z:ℂ=>U (0,z)),(fun z:ℂ=>W (0,z)),hU.curry_right,hW.curry_right,
    hU0,hW0,haxis.self_of_nhds.2.2.1,haxis.self_of_nhds.2.2.2,?_,ρ,C,hρ,hC,?_⟩
  · filter_upwards[hline.eventually hprops] with z hz
    exact ⟨hz.1,hz.2.1,hz.2.2.1⟩
  · intro z hz
    exact hclose 0 z (by simpa using hρ) hz
end WP.Analysis
