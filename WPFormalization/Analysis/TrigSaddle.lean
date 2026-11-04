import Mathlib
/-! The exact trigonometric density saddle.
The denominator is positive on (0, pi]. The derivative sign follows from
the positive second derivative 4 sin(t) (sin(t) - t cos(t)) of the
auxiliary numerator. A single use of L Hopital gives density limit three
at zero; continuity and strict monotonicity identify the original infimum. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

def trigDen (t:ℝ):ℝ:=Real.sin t-t*Real.cos t
def trigF (t:ℝ):ℝ:=t^2+t*Real.sin t*Real.cos t-2*(Real.sin t)^2
def trigJ (t:ℝ):ℝ:=2*t+t*((Real.cos t)^2-(Real.sin t)^2)-3*Real.sin t*Real.cos t
def densityTrig (t:ℝ):ℝ:=t^2*Real.sin t/trigDen t
lemma trigDen_hasDerivAt (t:ℝ):HasDerivAt trigDen (t*Real.sin t) t := by
  convert (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)) using 1
  · funext x
    rfl
  · simp <;> ring
lemma trigDen_continuous:Continuous trigDen:=by unfold trigDen;fun_prop
lemma trigDen_strictMono:StrictMonoOn trigDen (Icc 0 Real.pi):=by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) trigDen_continuous.continuousOn
  intro t ht
  rw[interior_Icc] at ht
  rw[(trigDen_hasDerivAt t).deriv]
  exact mul_pos ht.1 (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
lemma trigDen_pos (t:ℝ)(ht:t∈Ioc 0 Real.pi):0<trigDen t := by
  have hh:=trigDen_strictMono (show (0:ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩) ⟨ht.1.le,ht.2⟩ ht.1
  simpa[trigDen] using hh
lemma trigF_hasDerivAt (t:ℝ):HasDerivAt trigF (trigJ t) t:=by
  convert (((hasDerivAt_id t).pow 2).add (((hasDerivAt_id t).mul (Real.hasDerivAt_sin t)).mul (Real.hasDerivAt_cos t))).sub
    (((Real.hasDerivAt_sin t).pow 2).const_mul 2) using 1
  · funext x
    simp only [trigF,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq] <;> ring
  · simp [trigJ] <;> ring
lemma trigJ_hasDerivAt (t:ℝ):HasDerivAt trigJ (4*Real.sin t*trigDen t) t:=by
  convert (((hasDerivAt_id t).const_mul 2).add
    ((hasDerivAt_id t).mul (((Real.hasDerivAt_cos t).pow 2).sub ((Real.hasDerivAt_sin t).pow 2)))).sub
    (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).const_mul 3) using 1
  · funext x
    simp only [trigJ,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,id_eq] <;> ring
  · simp [trigDen] <;> nlinarith [Real.sin_sq_add_cos_sq t]
lemma trigJ_continuous:Continuous trigJ:=by unfold trigJ;fun_prop
lemma trigJ_strictMono:StrictMonoOn trigJ (Icc 0 Real.pi):=by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) trigJ_continuous.continuousOn
  intro t ht
  rw[interior_Icc] at ht
  rw[(trigJ_hasDerivAt t).deriv]
  exact mul_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)) (trigDen_pos t ⟨ht.1,ht.2.le⟩)
lemma trigJ_pos (t:ℝ)(ht:t∈Ioc 0 Real.pi):0<trigJ t := by
  have hh:=trigJ_strictMono (show (0:ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩) ⟨ht.1.le,ht.2⟩ ht.1
  simpa[trigJ] using hh
lemma trigF_continuous:Continuous trigF:=by unfold trigF;fun_prop
lemma trigF_strictMono:StrictMonoOn trigF (Icc 0 Real.pi):=by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) trigF_continuous.continuousOn
  intro t ht
  rw[interior_Icc] at ht
  rw[(trigF_hasDerivAt t).deriv]
  exact trigJ_pos t ⟨ht.1,ht.2.le⟩
lemma trigF_pos (t:ℝ)(ht:t∈Ioc 0 Real.pi):0<trigF t := by
  have hh:=trigF_strictMono (show (0:ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩) ⟨ht.1.le,ht.2⟩ ht.1
  simpa[trigF] using hh
lemma trigNumerator_hasDerivAt (t:ℝ):HasDerivAt (fun x:ℝ=>x^2*Real.sin x)
    (2*t*Real.sin t+t^2*Real.cos t) t:=by
  convert ((hasDerivAt_id t).pow 2).mul (Real.hasDerivAt_sin t) using 1
  · funext x
    rfl
  · simp only [Pi.pow_apply,id_eq]
    ring
lemma densityTrig_hasDerivAt (t:ℝ)(ht:t∈Ioo 0 Real.pi):
    HasDerivAt densityTrig (-t*trigF t/(trigDen t)^2) t:=by
  have hn:trigDen t≠0:=(trigDen_pos t ⟨ht.1,ht.2.le⟩).ne'
  have he:(2*t*Real.sin t+t^2*Real.cos t)*trigDen t-t^2*Real.sin t*(t*Real.sin t)= -t*trigF t:=by
    dsimp[trigDen,trigF]
    linear_combination -t^3*(Real.sin_sq_add_cos_sq t)
  convert (trigNumerator_hasDerivAt t).div (trigDen_hasDerivAt t) hn using 1
  · rfl
  · rw[he]
lemma densityTrig_continuousOn:ContinuousOn densityTrig (Ioc 0 Real.pi):=by
  apply ContinuousOn.div (by fun_prop) trigDen_continuous.continuousOn
  exact fun t ht=>(trigDen_pos t ht).ne'
lemma densityTrig_strictAnti:StrictAntiOn densityTrig (Ioo 0 Real.pi):=by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) (densityTrig_continuousOn.mono Ioo_subset_Ioc_self)
  intro t ht
  have ht':t∈Ioo 0 Real.pi:=by simpa only [isOpen_Ioo.interior_eq] using ht
  rw[(densityTrig_hasDerivAt t ht').deriv]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos ht'.1) (trigF_pos t ⟨ht'.1,ht'.2.le⟩))
    (sq_pos_of_pos (trigDen_pos t ⟨ht'.1,ht'.2.le⟩))
lemma densityTrig_pi:densityTrig Real.pi=0:=by simp[densityTrig,trigDen]
lemma densityTrig_limit_zero:Tendsto densityTrig (𝓝[>] (0:ℝ)) (𝓝 3):=by
  have hSin:Tendsto (fun t:ℝ=>Real.sin t/t) (𝓝[>] 0) (𝓝 1):=by
    have hh:=(Real.hasDerivAt_sin 0).tendsto_slope_zero_right
    simpa only [Real.cos_zero,zero_add,Real.sin_zero,sub_zero,smul_eq_mul,mul_comm,div_eq_mul_inv] using hh
  have hCos:Tendsto Real.cos (𝓝[>] (0:ℝ)) (𝓝 1):=by
    simpa only [Real.cos_zero] using (Real.continuous_cos.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim:Tendsto (fun t:ℝ=>2+Real.cos t/(Real.sin t/t)) (𝓝[>] 0) (𝓝 3):=by
    convert tendsto_const_nhds.add (hCos.div hSin (by norm_num : (1:ℝ)≠0)) using 1 <;> norm_num
  have hquot:Tendsto (fun t:ℝ=>(2*t*Real.sin t+t^2*Real.cos t)/(t*Real.sin t)) (𝓝[>] 0) (𝓝 3):=by
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with t ht
    have ht0:t≠0:=ht.1.ne'
    have hs0:Real.sin t≠0:=(Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    field_simp
    <;>ring
  have hn:Tendsto (fun t:ℝ=>t^2*Real.sin t) (𝓝[>] 0) (𝓝 0):=by
    have hc:ContinuousAt (fun t:ℝ=>t^2*Real.sin t) 0:=by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hd:Tendsto trigDen (𝓝[>] (0:ℝ)) (𝓝 0):=by
    simpa[trigDen] using (trigDen_continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  exact HasDerivAt.lhopital_zero_right_on_Ioo Real.pi_pos
    (fun t _=>trigNumerator_hasDerivAt t) (fun t _=>trigDen_hasDerivAt t)
    (fun t ht=>mul_ne_zero ht.1.ne' (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne') hn hd hquot
end WP.Analysis
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma densityTrig_unique (u:ℝ)(hu:u∈Ioo 0 3):
    ∃!t:ℝ,t∈Ioo 0 Real.pi ∧densityTrig t=u := by
  have he:∀ᶠt in 𝓝[>] (0:ℝ),u<densityTrig t:=densityTrig_limit_zero.eventually (Ioi_mem_nhds hu.2)
  obtain ⟨a,ha,haf⟩:=((show ∀ᶠt in 𝓝[>] (0:ℝ),t∈Ioo 0 Real.pi from Ioo_mem_nhdsGT Real.pi_pos).and he).exists
  have hc:ContinuousOn densityTrig (Icc a Real.pi):=densityTrig_continuousOn.mono
    (fun t ht=>⟨lt_of_lt_of_le ha.1 ht.1,ht.2⟩)
  obtain ⟨t,ht,hroot⟩:=intermediate_value_Icc' ha.2.le hc
    (show u∈Icc (densityTrig Real.pi) (densityTrig a) from ⟨by rw[densityTrig_pi];exact hu.1.le,haf.le⟩)
  have ht0:0<t:=lt_of_lt_of_le ha.1 ht.1
  have htπ:t<Real.pi:=lt_of_le_of_ne ht.2 (by
    intro he
    rw[he,densityTrig_pi] at hroot
    linarith[hu.1])
  refine ⟨t,⟨⟨ht0,htπ⟩,hroot⟩,?_⟩
  intro x hx
  exact densityTrig_strictAnti.injOn hx.1 ⟨ht0,htπ⟩ (hx.2.trans hroot.symm)

lemma densityTrig_sInf_spec (u:ℝ)(hu:u∈Ioo 0 3):
    let s:=sInf {t:ℝ|t∈Ioo 0 Real.pi ∧densityTrig t=u}
    s∈Ioo 0 Real.pi ∧densityTrig s=u ∧∀t∈Ioo 0 Real.pi,densityTrig t=u→t=s := by
  obtain ⟨t,ht,huniq⟩:=densityTrig_unique u hu
  have hset:{x:ℝ|x∈Ioo 0 Real.pi ∧densityTrig x=u}={t}:=by
    ext x
    constructor
    · intro hx
      exact Set.mem_singleton_iff.mpr (huniq x hx)
    · intro hx
      have he:x=t:=Set.mem_singleton_iff.mp hx
      subst x
      exact ht
  dsimp only
  rw[hset,csInf_singleton]
  refine ⟨ht.1,ht.2,?_⟩
  intro x hx hf
  exact huniq x ⟨hx,hf⟩

lemma trig_saddle_spec_proof (g k:ℕ)(hg:1≤g)(hk:k<3*g-2):
    let s:=sInf {t:ℝ|t∈Ioo 0 Real.pi ∧densityTrig t=(2*(k:ℝ)+1)/(2*(g:ℝ)-1)}
    s∈Ioo 0 Real.pi ∧densityTrig s=(2*(k:ℝ)+1)/(2*(g:ℝ)-1) ∧
    (∀t∈Ioo 0 Real.pi,densityTrig t=(2*(k:ℝ)+1)/(2*(g:ℝ)-1)→t=s) := by
  apply densityTrig_sInf_spec
  have hgR:(1:ℝ)≤g:=by exact_mod_cast hg
  have hden:0<2*(g:ℝ)-1:=by linarith
  constructor
  · exact div_pos (by positivity) hden
  · apply (div_lt_iff₀ hden).mpr
    have hk':2*k+1<6*g-3:=by omega
    have hsub:3≤6*g:=by omega
    have hreal:2*(k:ℝ)+1<6*(g:ℝ)-3:=by
      have hh:((2*k+1:ℕ):ℝ)<((6*g-3:ℕ):ℝ):=by exact_mod_cast hk'
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,Nat.cast_sub hsub] using hh
    linarith
end WP.Analysis
