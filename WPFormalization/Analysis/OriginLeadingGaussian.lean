import WPFormalization.Analysis.PoissonSecondRemainder
import WPFormalization.Analysis.CoefficientSubstitution
import WPFormalization.Analysis.CoefficientScaling
import WPFormalization.Volumes.CriticalPuiseux
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma second_saddle_remainder_diagonal (S:ℂ→ℂ) (D:ℂ × ℂ → ℂ)
    (hS:AnalyticAt ℂ S 0) (hD:AnalyticAt ℂ D 0)
    (hfac:∀ᶠv:ℂ × ℂ in 𝓝 0,S v.1-S v.2-(v.1-v.2)*deriv S v.2=(v.1-v.2)^2*D v):
    ∀ᶠx:ℂ in 𝓝 0,D (x,x)=iteratedDeriv 2 S x/2:=by
  have hdiag:Tendsto (fun x:ℂ=>(x,x)) (𝓝 0) (𝓝 (0:ℂ × ℂ)):=by
    exact (continuous_id.prodMk continuous_id).continuousAt.tendsto
  filter_upwards[hS.eventually_analyticAt,hdiag.eventually hD.eventually_analyticAt,
    hdiag.eventually hfac.eventually_nhds] with x hSx hDx hloc
  let f:ℂ→ℂ:=fun t=>S (x+t)-S x-t*deriv S x
  let g:ℂ→ℂ:=fun t=>D (x+t,x)
  have hTx:AnalyticAt ℂ (fun t:ℂ=>(x+t,x)) 0:=
    (analyticAt_const.add analyticAt_id).prod analyticAt_const
  have hTx0:((x+(0:ℂ),x):ℂ × ℂ)=(x,x):=by simp
  have hg:AnalyticAt ℂ g 0:=by
    have hd:AnalyticAt ℂ D (x+0,x):=by simpa only[add_zero] using hDx
    exact hd.comp (f:=fun t:ℂ=>(x+t,x)) hTx
  have hT:Tendsto (fun t:ℂ=>(x+t,x)) (𝓝 0) (𝓝 (x,x)):=by
    simpa only[add_zero] using hTx.continuousAt.tendsto
  have he:f=ᶠ[𝓝 0] (fun t:ℂ=>t^2*g t):=by
    filter_upwards[hT.eventually hloc] with t ht
    simpa only[sub_self,add_sub_cancel_left,Prod.fst,Prod.snd,f,g] using ht
  have hcoef:WP.coeff f 2=D (x,x):=by
    rw[coeff_congr_of_eventuallyEq _ _ he,coeff_id_pow_mul g hg 2 2]
    simp only[le_refl,ite_true,Nat.sub_self,WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,g,add_zero]
  have hSshift:AnalyticAt ℂ (fun t:ℂ=>S (x+t)) 0:=by
    have hh:AnalyticAt ℂ S (x+0):=by simpa only[add_zero] using hSx
    exact hh.comp (f:=fun t:ℂ=>x+t) (analyticAt_const.add analyticAt_id)
  have hsub:ContDiffAt ℂ 2 (fun t:ℂ=>S (x+t)-S x) 0:=(hSshift.sub analyticAt_const).contDiffAt
  have hlin:ContDiffAt ℂ 2 (fun t:ℂ=>t*deriv S x) 0:=by fun_prop
  have hj:iteratedDeriv 2 f 0=iteratedDeriv 2 S x:=by
    rw[show f=(fun t:ℂ=>(S (x+t)-S x)-(t*deriv S x)) from rfl]
    rw[iteratedDeriv_fun_sub hsub hlin,
      iteratedDeriv_fun_sub hSshift.contDiffAt (by fun_prop),iteratedDeriv_mul_const_field]
    simp only[iteratedDeriv_const,iteratedDeriv_fun_id_zero]
    norm_num[iteratedDeriv_comp_const_add]
  rw[←hcoef,WP.coeff,hj]
  norm_num
end WP.Analysis
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma analytic_exp_second_unit:
    ∃E:ℂ→ℂ,AnalyticAt ℂ E 0∧E 0=1/2∧∀ᶠu:ℂ in 𝓝 0,Complex.exp u=1+u+u^2*E u:=by
  have hExp:AnalyticAt ℂ Complex.exp 0:=Complex.differentiable_exp.analyticAt 0
  obtain ⟨E₃,hE₃,hE₃eq⟩:=hExp.exists_eventuallyEq_sum_add_pow_mul 3
  let E:ℂ→ℂ:=fun u=>1/2+u*E₃ u
  refine ⟨E,analyticAt_const.add (analyticAt_id.mul hE₃),by simp[E],?_⟩
  filter_upwards[hE₃eq] with u hu
  simp only[Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    Nat.factorial_zero,Nat.factorial_one,Nat.factorial_two,Nat.cast_one,Nat.cast_ofNat,
    div_one,iteratedDeriv_eq_iterate,Complex.iter_deriv_exp,Complex.exp_zero,
    smul_eq_mul,mul_one] at hu
  dsimp[E]
  linear_combination hu
lemma origin_leading_gaussian_local_data (S Bc:ℂ→ℂ)
    (hS:AnalyticAt ℂ S 0) (hSd:deriv S 0=2)
    (hBc:AnalyticAt ℂ Bc 0) (hBc0:Bc 0≠0):
    ∃(G Amp J:ℂ × ℂ → ℂ)(q:ℂ→ℂ)(ρ C:ℝ),0<ρ∧0<C∧
      AnalyticAt ℂ q 0∧(∀x:ℂ,q x=(Complex.sqrt (deriv S x+x*iteratedDeriv 2 S x))⁻¹)∧
      (∀x:ℂ,‖x‖≤ρ→q x^2*(deriv S x+x*iteratedDeriv 2 S x)=1∧Amp (x,0)=1∧J (x,0)=1/2)∧
      ∀x u:ℂ,‖x‖≤ρ→‖u‖≤ρ→
        AnalyticAt ℂ G (x,u)∧AnalyticAt ℂ Amp (x,u)∧
        G (x,u)=u^2*J (x,u)∧‖G (x,u)‖≤C*‖u‖^2∧‖Amp (x,u)‖≤C∧
        S (x*Complex.exp (u*q x))-S x-x*deriv S x*(u*q x)=x*G (x,u)∧
        Amp (x,u)=Bc (x*Complex.exp (u*q x))/Bc x∧
        WP.coeff (fun v:ℂ=>G (x,v)) 0=0∧WP.coeff (fun v:ℂ=>G (x,v)) 1=0∧
        WP.coeff (fun v:ℂ=>G (x,v)) 2=1/2:=by
  obtain ⟨D,hD,hD0,hfac⟩:=analytic_second_saddle_remainder S hS (fun x:ℂ=>x) analyticAt_id rfl
  have hfac':∀ᶠv:ℂ × ℂ in 𝓝 0,S v.1-S v.2-(v.1-v.2)*deriv S v.2=(v.1-v.2)^2*D v:=hfac
  have hDdiag:=second_saddle_remainder_diagonal S D hS hD hfac'
  obtain ⟨E,hE,hE0,hEe⟩:=analytic_exp_second_unit
  let V:ℂ→ℂ:=fun x=>deriv S x+x*iteratedDeriv 2 S x
  have hV:AnalyticAt ℂ V 0:=by
    have hd2:AnalyticAt ℂ (iteratedDeriv 2 S) 0:=by
      simpa only[iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hS.deriv.deriv
    exact hS.deriv.add (analyticAt_id.mul hd2)
  have hV0:V 0=2:=by simp only[V,zero_mul,add_zero,hSd]
  have hroot:AnalyticAt ℂ (fun x=>Complex.sqrt (V x)) 0:=
    (complex_sqrt_analyticAt (by rw[hV0];exact Or.inl (by norm_num))).comp hV
  have hroot0:Complex.sqrt (V 0)≠0:=by
    intro hz
    have he:=complex_sqrt_sq (V 0)
    rw[hz,zero_pow (by omega:2≠0),hV0] at he
    norm_num at he
  let q:ℂ→ℂ:=fun x=>(Complex.sqrt (V x))⁻¹
  have hq:AnalyticAt ℂ q 0:=hroot.inv hroot0
  have hqv:∀ᶠx:ℂ in 𝓝 0,(q x)^2*V x=1:=by
    filter_upwards[hroot.continuousAt.eventually_ne hroot0] with x hx
    dsimp[q]
    calc
      _ = (Complex.sqrt (V x))⁻¹^2*(Complex.sqrt (V x))^2 := by rw[complex_sqrt_sq]
      _ = 1 := by field_simp
  let E₁:ℂ→ℂ:=fun u=>1+u*E u
  have hE₁:AnalyticAt ℂ E₁ 0:=analyticAt_const.add (analyticAt_id.mul hE)
  have hE₁0:E₁ 0=1:=by simp[E₁]
  let t:ℂ × ℂ → ℂ:=fun v=>v.2*q v.1
  have hqf:AnalyticAt ℂ (fun v:ℂ × ℂ=>q v.1) 0:=
    AnalyticAt.comp (g:=q) (f:=fun v:ℂ × ℂ=>v.1) (x:=(0:ℂ × ℂ)) hq analyticAt_fst
  have ht:AnalyticAt ℂ t 0:=analyticAt_snd.mul hqf
  have ht0:t 0=0:=by simp[t]
  let N:ℂ × ℂ → ℂ × ℂ:=fun v=>(v.1*Complex.exp (t v),v.1)
  have hN:AnalyticAt ℂ N 0:=(analyticAt_fst.mul ht.cexp).prod analyticAt_fst
  have hN0:N 0=0:=by simp[N]
  let J:ℂ × ℂ → ℂ:=fun v=>(q v.1)^2*(deriv S v.1*E (t v)+v.1*(E₁ (t v))^2*D (N v))
  have hJa:AnalyticAt ℂ J 0:=by
    have hEc:AnalyticAt ℂ E (t 0):=by rw[ht0];exact hE
    have hE₁c:AnalyticAt ℂ E₁ (t 0):=by rw[ht0];exact hE₁
    have hDc:AnalyticAt ℂ D (N 0):=by rw[hN0];exact hD
    have hSf:AnalyticAt ℂ (fun v:ℂ × ℂ=>deriv S v.1) 0:=
      AnalyticAt.comp (g:=deriv S) (f:=fun v:ℂ × ℂ=>v.1) (x:=(0:ℂ × ℂ)) hS.deriv analyticAt_fst
    exact (hqf.pow 2).mul
      ((hSf.mul (hEc.comp ht)).add
        ((analyticAt_fst.mul ((hE₁c.comp ht).pow 2)).mul (hDc.comp hN)))
  let G:ℂ × ℂ → ℂ:=fun v=>v.2^2*J v
  have hGa:AnalyticAt ℂ G 0:=(analyticAt_snd.pow 2).mul hJa
  let Amp:ℂ × ℂ → ℂ:=fun v=>Bc (N v).1/Bc v.1
  have hNa:AnalyticAt ℂ (fun v:ℂ × ℂ=>(N v).1) 0:=analyticAt_fst.comp hN
  have hAa:AnalyticAt ℂ Amp 0:=by
    have hBN:AnalyticAt ℂ Bc (N 0).1:=by rw[hN0];exact hBc
    have hnum:AnalyticAt ℂ (fun v:ℂ × ℂ=>Bc (N v).1) 0:=
      AnalyticAt.comp (g:=Bc) (f:=fun v:ℂ × ℂ=>(N v).1) (x:=(0:ℂ × ℂ)) hBN hNa
    have hden:AnalyticAt ℂ (fun v:ℂ × ℂ=>Bc v.1) 0:=
      AnalyticAt.comp (g:=Bc) (f:=fun v:ℂ × ℂ=>v.1) (x:=(0:ℂ × ℂ)) hBc analyticAt_fst
    exact hnum.div hden hBc0
  have hJaxis:∀ᶠx:ℂ in 𝓝 0,J (x,0)=1/2:=by
    filter_upwards[hDdiag,hqv] with x hd hqv
    simp only[J,t,N,zero_mul,Complex.exp_zero,mul_one,E₁,hE0,zero_add,one_pow,hd]
    dsimp[V] at hqv
    linear_combination hqv/2
  have hAaxis:∀ᶠx:ℂ in 𝓝 0,Amp (x,0)=1:=by
    filter_upwards[hBc.continuousAt.eventually_ne hBc0] with x hx
    simp only[Amp,N,t,zero_mul,Complex.exp_zero,mul_one]
    exact div_self hx
  have hNt:Tendsto N (𝓝 0) (𝓝 (0:ℂ × ℂ)):=by simpa only[hN0] using hN.continuousAt.tendsto
  have htt:Tendsto t (𝓝 0) (𝓝 (0:ℂ)):=by simpa only[ht0] using ht.continuousAt.tendsto
  have hphase:∀ᶠv:ℂ × ℂ in 𝓝 0,
      S (v.1*Complex.exp (v.2*q v.1))-S v.1-v.1*deriv S v.1*(v.2*q v.1)=v.1*G v:=by
    filter_upwards[hNt.eventually hfac',htt.eventually hEe] with v hd he
    let x:ℂ:=v.1
    let w:ℂ:=v.2*q v.1
    have he':Complex.exp w=1+w+w^2*E w:=he
    change S (x*Complex.exp w)-S x-(x*Complex.exp w-x)*deriv S x=
      (x*Complex.exp w-x)^2*D (x*Complex.exp w,x) at hd
    change S (x*Complex.exp w)-S x-x*deriv S x*w=x*G v
    calc
      _ = (x*Complex.exp w-x)*deriv S x+(x*Complex.exp w-x)^2*D (x*Complex.exp w,x)-x*deriv S x*w := by linear_combination hd
      _ = _ := by
        dsimp[G,J,N,t,E₁]
        change (x*Complex.exp w-x)*deriv S x+(x*Complex.exp w-x)^2*D (x*Complex.exp w,x)-x*deriv S x*w=
          x*(v.2^2*((q x)^2*(deriv S x*E w+x*(1+w*E w)^2*D (x*Complex.exp w,x))))
        rw[he']
        dsimp[w]
        ring
  have hbounds:∀ᶠv:ℂ × ℂ in 𝓝 0,AnalyticAt ℂ J v∧AnalyticAt ℂ G v∧AnalyticAt ℂ Amp v∧
      ‖J v‖<‖J 0‖+1∧‖Amp v‖<‖Amp 0‖+1:=by
    filter_upwards[hJa.eventually_analyticAt,hGa.eventually_analyticAt,hAa.eventually_analyticAt,
      hJa.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (lt_add_one _)),
      hAa.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (lt_add_one _))] with v hj hg ha hbj hba
    exact ⟨hj,hg,ha,hbj,hba⟩
  obtain ⟨r,hr,hrloc⟩:=Metric.eventually_nhds_iff.mp (hbounds.and hphase)
  obtain ⟨s,hs,hsloc⟩:=Metric.eventually_nhds_iff.mp ((hqv.and hAaxis).and hJaxis)
  let ρ:ℝ:=min (r/2) (s/2)
  let C:ℝ:=max (‖J 0‖+1) (‖Amp 0‖+1)
  have hρ:0<ρ:=lt_min (half_pos hr) (half_pos hs)
  have hρr:ρ<r:=(min_le_left _ _).trans_lt (half_lt_self hr)
  have hρs:ρ<s:=(min_le_right _ _).trans_lt (half_lt_self hs)
  have hC:0<C:=(by positivity:0<‖J 0‖+1).trans_le (le_max_left _ _)
  refine ⟨G,Amp,J,q,ρ,C,hρ,hC,hq,(fun x=>rfl),?_,?_⟩
  · intro x hx
    have hl:=hsloc (by simpa only[dist_zero_right] using hx.trans_lt hρs)
    exact ⟨hl.1.1,hl.1.2,hl.2⟩
  · intro x u hx hu
    have hn:‖(x,u)‖<r:=by rw[Prod.norm_def];exact max_lt (hx.trans_lt hρr) (hu.trans_lt hρr)
    have hl:=hrloc (by simpa only[dist_zero_right] using hn)
    have hsmall:‖(x,(0:ℂ))‖<r:=by rw[Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)];exact hx.trans_lt hρr
    have hjx:AnalyticAt ℂ (fun v:ℂ=>J (x,v)) 0:=
      (hrloc (by simpa only[dist_zero_right] using hsmall)).1.1.comp (f:=fun v:ℂ=>(x,v)) (analyticAt_const.prod analyticAt_id)
    have haxis:=hsloc (by simpa only[dist_zero_right] using hx.trans_lt hρs)
    refine ⟨hl.1.2.1,hl.1.2.2.1,rfl,?_,?_,hl.2,rfl,?_,?_,?_⟩
    · dsimp[G]
      rw[norm_mul,norm_pow]
      have hb:‖J (x,u)‖≤C:=hl.1.2.2.2.1.le.trans (le_max_left _ _)
      nlinarith[mul_le_mul_of_nonneg_left hb (sq_nonneg ‖u‖)]
    · exact hl.1.2.2.2.2.le.trans (le_max_right _ _)
    · rw[show (fun v:ℂ=>G (x,v))=(fun v:ℂ=>v^2*J (x,v)) from rfl,coeff_id_pow_mul _ hjx 2 0]
      simp
    · rw[show (fun v:ℂ=>G (x,v))=(fun v:ℂ=>v^2*J (x,v)) from rfl,coeff_id_pow_mul _ hjx 2 1]
      simp
    · rw[show (fun v:ℂ=>G (x,v))=(fun v:ℂ=>v^2*J (x,v)) from rfl,coeff_id_pow_mul _ hjx 2 2]
      simpa only[le_refl,ite_true,Nat.sub_self,WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one] using haxis.2
end WP.Analysis
