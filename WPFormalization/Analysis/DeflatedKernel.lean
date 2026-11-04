import WPFormalization.Analysis.KernelZeros
import WPFormalization.Analysis.HKernelUniform
import WPFormalization.Analysis.ParameterDerivative
import WPFormalization.Analysis.HarmonicProbability

/-! The actual normalized K family after removing its first zero. The
integral of the derivative gives a joint continuous entire extension at w=1
and the critical endpoint. The proved root classification and compactness
then give a common zero-free disk of radius strictly greater than one.
No weight coefficient positivity or uniform moment bound is assumed. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
set_option maxHeartbeats 600000 in
lemma barK_joint_continuous : Continuous (fun p : Icc (0:ℝ) y₀ × ℂ => barK (p.1:ℝ) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hpe : (p.1:ℝ)=y₀
  · apply Metric.continuousAt_iff.mpr
    intro ε hε
    let R : ℝ := ‖p.2‖+1
    have hR : 0<R := by dsimp [R]; positivity
    obtain ⟨δY,hδY,hYbound⟩ := Metric.mem_nhdsWithin_iff.mp (critical_normalized_kernels_uniform R hR (ε/2) (by positivity))
    have hg : ContinuousAt (fun w:ℂ => 1-w) p.2 := by fun_prop
    obtain ⟨δw,hδw,hwbound⟩ := Metric.continuousAt_iff.mp hg (ε/2) (by positivity)
    refine ⟨min δY (min δw 1),by positivity,?_⟩
    intro q hq
    have hdY : dist (q.1:ℝ) y₀ < δY := by
      have hh : dist q.1 p.1 < δY := lt_of_le_of_lt (show dist q.1 p.1 ≤ dist q p by rw [Prod.dist_eq]; exact le_max_left _ _) (lt_of_lt_of_le hq (min_le_left _ _))
      simpa only [Subtype.dist_eq,hpe] using hh
    have hdw : dist q.2 p.2 < min δw 1 :=
      lt_of_le_of_lt (show dist q.2 p.2 ≤ dist q p by rw [Prod.dist_eq]; exact le_max_right _ _) (lt_of_lt_of_le hq (min_le_right _ _))
    have hqR : ‖q.2‖≤R := by
      have hn := norm_le_norm_add_norm_sub p.2 q.2
      dsimp [R]
      rw [← dist_eq_norm,dist_comm p.2 q.2] at hn
      linarith [lt_of_lt_of_le hdw (min_le_right _ _)]
    have hlin := hwbound (lt_of_lt_of_le hdw (min_le_left _ _))
    have happrox : ‖barK (q.1:ℝ) q.2-(1-q.2)‖≤ε/2 := by
      by_cases heq : (q.1:ℝ)=y₀
      · simp only [barK,if_pos heq,sub_self,norm_zero]
        positivity
      · exact (hYbound ⟨hdY,lt_of_le_of_ne q.1.property.2 heq⟩ q.2 hqR).1
    have htri := norm_sub_le_norm_sub_add_norm_sub (barK (q.1:ℝ) q.2) (1-q.2) (1-p.2)
    rw [dist_eq_norm] at hlin ⊢
    rw [show barK (p.1:ℝ) p.2 = 1-p.2 by simp [barK,hpe]]
    linarith
  · have hpI : (p.1:ℝ) ∈ Ico 0 y₀ := ⟨p.1.property.1,lt_of_le_of_ne p.1.property.2 hpe⟩
    have hlt : ∀ᶠ q : Icc (0:ℝ) y₀ × ℂ in 𝓝 p, (q.1:ℝ)<y₀ :=
      (show ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => (q.1:ℝ)) p by fun_prop).tendsto.eventually (gt_mem_nhds hpI.2)
    have hmap : Tendsto (fun q : Icc (0:ℝ) y₀ × ℂ => (q.1:ℝ)) (𝓝 p) (𝓝[Ico 0 y₀] (p.1:ℝ)) := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun q : Icc (0:ℝ) y₀ × ℂ => (q.1:ℝ))
      (show ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => (q.1:ℝ)) p by fun_prop)
      (hlt.mono (fun q hq => ⟨q.1.property.1,hq⟩))
    have hrOn : ContinuousOn r (Ico (0:ℝ) y₀) := continuousOn_iff_continuous_restrict.mpr r_continuous_interior
    have hr : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => r (q.1:ℝ)) p := (hrOn _ hpI).tendsto.comp hmap
    have hyc : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => ((q.1:ℝ):ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp (continuous_subtype_val.continuousAt.comp continuous_fst.continuousAt)
    have hrc : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => (r (q.1:ℝ):ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp hr
    have hzc : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => (r (q.1:ℝ):ℂ)*q.2) p := hrc.mul continuous_snd.continuousAt
    have hpair : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => (((q.1:ℝ):ℂ),(r (q.1:ℝ):ℂ)*q.2)) p := hyc.prodMk hzc
    have hn : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => K (q.1:ℝ) ((r (q.1:ℝ):ℂ)*q.2)) p :=
      K_joint_continuous.continuousAt.comp (f := fun q : Icc (0:ℝ) y₀ × ℂ => (((q.1:ℝ):ℂ),(r (q.1:ℝ):ℂ)*q.2)) hpair
    have had : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => (a (q.1:ℝ):ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp (a_continuous.continuousAt.comp (continuous_subtype_val.continuousAt.comp continuous_fst.continuousAt))
    have hc : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => K (q.1:ℝ) ((r (q.1:ℝ):ℂ)*q.2)/(a (q.1:ℝ):ℂ)) p :=
      hn.div had (by exact_mod_cast a_ne_zero p.1 hpI)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hlt] with q hq
    simp only [barK,if_neg (ne_of_lt hq)]

lemma barK_derivative_joint_continuous :
    Continuous (fun p:Icc (0:ℝ) y₀ × ℂ=>deriv (barK (p.1:ℝ)) p.2) :=
  parameter_derivative_joint_continuous (fun Y:Icc (0:ℝ) y₀=>barK (Y:ℝ))
    (fun Y=>barK_differentiable (Y:ℝ)) barK_joint_continuous

def deflatedBarK (Y:ℝ) (w:ℂ) : ℂ :=
  -(∫ s:ℝ in (0)..1,deriv (barK Y) (1+(s:ℂ)*(w-1)))
lemma deflatedBarK_identity (Y:ℝ) (hY:Y∈Icc 0 y₀) (w:ℂ) :
    (1-w)*deflatedBarK Y w=barK Y w := by
  have hg:Differentiable ℂ (barK Y):=barK_differentiable Y
  have hd (s:ℝ):HasDerivAt (fun u:ℝ=>barK Y (1+(u:ℂ)*(w-1)))
      ((w-1)*deriv (barK Y) (1+(s:ℂ)*(w-1))) s := by
    have hh:HasDerivAt (fun u:ℂ=>barK Y (1+u*(w-1)))
        ((w-1)*deriv (barK Y) (1+(s:ℂ)*(w-1))) (s:ℂ) := by
      convert (hg _).hasDerivAt.comp (s:ℂ) (((hasDerivAt_id (s:ℂ)).mul_const (w-1)).const_add 1) using 1
      · rfl
      · dsimp;ring
    exact hh.comp_ofReal
  have hc:Continuous (fun s:ℝ=>(w-1)*deriv (barK Y) (1+(s:ℂ)*(w-1))) := by
    have hh:Continuous (deriv (barK Y)):=hg.deriv.continuous
    fun_prop
  have hFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (fun s _=>hd s) (hc.intervalIntegrable 0 1)
  simp only [Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul,add_zero,
    add_sub_cancel,barK_one_zero Y hY,sub_zero] at hFTC
  rw [intervalIntegral.integral_const_mul] at hFTC
  unfold deflatedBarK
  linear_combination hFTC
lemma deflatedBarK_joint_continuous :
    Continuous (fun p:Icc (0:ℝ) y₀ × ℂ=>deflatedBarK (p.1:ℝ) p.2) := by
  let F:(Icc (0:ℝ) y₀ × ℂ)→ℝ→ℂ:=
    fun p s=>deriv (barK (p.1:ℝ)) (1+(s:ℂ)*(p.2-1))
  have hF:Continuous (fun p:(Icc (0:ℝ) y₀ × ℂ)×ℝ=>F p.1 p.2) := by
    have hmap:Continuous (fun p:(Icc (0:ℝ) y₀ × ℂ)×ℝ=>
      (p.1.1,1+(p.2:ℂ)*(p.1.2-1))) := by fun_prop
    exact barK_derivative_joint_continuous.comp hmap
  have hi:=continuous_parametric_integral_of_continuous
    (X:=Icc (0:ℝ) y₀ × ℂ) (Y:=ℝ) (E:=ℂ) (f:=F) (μ:=volume) hF (s:=Icc (0:ℝ) 1) isCompact_Icc
  have hi':Continuous (fun p:Icc (0:ℝ) y₀ × ℂ=>∫ s:ℝ in (0)..1,F p s) := by
    convert hi using 1
    ext p
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one]
  exact hi'.neg
lemma deflatedBarK_critical (w:ℂ):deflatedBarK y₀ w=1 := by
  have hf:barK y₀=(fun z:ℂ=>1-z) := by funext z;simp [barK]
  have hd (z:ℂ):deriv (barK y₀) z= -1 := by
    rw [hf]
    exact ((hasDerivAt_id z).const_sub 1).deriv
  simp [deflatedBarK,hd]
lemma barK_deriv_interior (Y:ℝ) (hY:Y∈Ico 0 y₀) (w:ℂ) :
    deriv (barK Y) w=(r Y:ℂ)*deriv (K Y) ((r Y:ℂ)*w)/(a Y:ℂ) := by
  have he:barK Y=(fun z:ℂ=>K Y ((r Y:ℂ)*z)/(a Y:ℂ)) := by
    funext z
    simp only [barK,if_neg (ne_of_lt hY.2)]
  rw [he]
  have hd:=(((K_differentiable Y _).hasDerivAt.comp w
    ((hasDerivAt_id w).const_mul (r Y:ℂ))).div_const (a Y:ℂ)).deriv
  dsimp only [id_eq,Function.comp_def] at hd
  convert hd using 1
  ring
lemma deflatedBarK_one (Y:ℝ):deflatedBarK Y 1= -deriv (barK Y) 1 := by
  simp [deflatedBarK]
lemma deflatedBarK_zero_free_unit (Y:ℝ) (hY:Y∈Icc 0 y₀) (w:ℂ) (hw:‖w‖≤1) :
    deflatedBarK Y w≠0 := by
  by_cases he:Y=y₀
  · subst Y
    rw [deflatedBarK_critical]
    norm_num
  have hYi:Y∈Ico 0 y₀:=⟨hY.1,lt_of_le_of_ne hY.2 he⟩
  have hr:0<r Y:=r_pos Y hYi
  have hrc:(r Y:ℂ)≠0:=by exact_mod_cast hr.ne'
  have hac:(a Y:ℂ)≠0:=by exact_mod_cast a_ne_zero Y hYi
  by_cases hw1:w=1
  · subst w
    rw [deflatedBarK_one,neg_ne_zero,barK_deriv_interior Y hYi 1,mul_one]
    exact div_ne_zero (mul_ne_zero hrc (K_deriv_at_r_ne_zero Y hYi)) hac
  intro hzero
  have hb:barK Y w=0:=by rw [←deflatedBarK_identity Y hY,hzero,mul_zero]
  simp only [barK,if_neg he] at hb
  have hK:K Y ((r Y:ℂ)*w)=0 := by
    have hh:=congrArg (fun z:ℂ=>z*(a Y:ℂ)) hb
    field_simp at hh
    simpa only [mul_zero] using hh
  obtain ⟨q,hmono,hpos,hfirst,hall,_⟩:=K_ordered_simple_zeros Y hYi
  obtain ⟨j,hj⟩:=(hall ((r Y:ℂ)*w)).mp hK
  have hge:r Y≤q j:=by rw [←hfirst];exact hmono.monotone (Nat.zero_le j)
  have hn:=congrArg norm hj
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos j)] at hn
  have heq:q j=r Y:=by nlinarith
  apply hw1
  apply (mul_left_cancel₀ hrc)
  rw [mul_one,hj,heq]
lemma deflatedBarK_differentiable (Y:ℝ):Differentiable ℂ (deflatedBarK Y) := by
  let g:ℂ→ℂ:=deriv (barK Y)
  have hg:Differentiable ℂ g:=(barK_differentiable Y).deriv
  have he:deflatedBarK Y=(fun w:ℂ=> -(∫ s:ℝ in (0)..1,g (1-(s:ℂ)+w*(s:ℂ)))) := by
    funext w
    unfold deflatedBarK
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    apply congrArg g
    ring
  rw [he]
  intro w
  have hd:=hasDerivAt_affineIntegral (fun _=>1) (fun s:ℝ=>1-(s:ℂ))
    (fun s:ℝ=>(s:ℂ)) continuous_const (by fun_prop) (by fun_prop) g hg w
  convert hd.neg.differentiableAt using 1 <;> simp only [one_mul] <;> rfl
lemma deflatedBarK_uniform_zero_free : ∃ η:ℝ,0<η ∧ ∀ Y∈Icc (0:ℝ) y₀, ∀ w:ℂ, ‖w‖≤1+η → deflatedBarK Y w≠0 := by
  let S : Set (Icc (0:ℝ) y₀ × ℂ) := univ ×ˢ Metric.closedBall 0 1
  have hS : IsCompact S := isCompact_univ.prod (isCompact_closedBall 0 1)
  let U : Set (Icc (0:ℝ) y₀ × ℂ) := {p | deflatedBarK (p.1:ℝ) p.2≠0}
  have hU : IsOpen U := isOpen_ne_fun deflatedBarK_joint_continuous continuous_const
  have hSU : S⊆U := by
    intro p hp
    exact deflatedBarK_zero_free_unit p.1 p.1.property p.2 (by simpa only [S,mem_prod,mem_univ,mem_closedBall_zero_iff,and_true,true_and] using hp)
  obtain ⟨δ,hδ,hth⟩ := hS.exists_thickening_subset_open hU hSU
  refine ⟨δ/2,by positivity,?_⟩
  intro Y hY w hw
  let v : ℂ := w/((1+δ/2:ℝ):ℂ)
  have hden : 0<1+δ/2 := by linarith
  have hv : ‖v‖≤1 := by
    dsimp [v]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hden]
    exact (div_le_one hden).mpr hw
  have hd : dist w v<δ := by
    have he : w-v = ((δ/2:ℝ):ℂ)*v := by
      dsimp [v]
      have hd0 : ((1+δ/2:ℝ):ℂ) ≠0 := by exact_mod_cast ne_of_gt hden
      have hdc : 1+(δ:ℂ)/2≠0 := by exact_mod_cast ne_of_gt hden
      push_cast
      field_simp [hdc,show (2+(δ:ℂ))≠0 by exact_mod_cast (show (2:ℝ)+δ≠0 by linarith)]
      ring
    rw [dist_eq_norm,he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<δ/2)]
    nlinarith
  change (⟨Y,hY⟩,w)∈U
  apply hth
  rw [Metric.mem_thickening_iff]
  refine ⟨(⟨Y,hY⟩,v),⟨mem_univ _,by simpa only [Metric.mem_closedBall,dist_zero_right] using hv⟩,?_⟩
  simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hd
end WP.Analysis
