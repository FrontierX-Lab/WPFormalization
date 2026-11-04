import WPFormalization.Analysis.HKernelZeroFree
import Mathlib.Topology.MetricSpace.Thickening
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma H_joint_continuous : Continuous (fun (p : ℂ × ℂ) => H p.1 p.2) := by
  have hh := kernelIntegral_continuous_joint (fun s:ℝ => (s:ℂ)^2) (by fun_prop) (deriv X) (X_differentiable.deriv.continuous)
  change Continuous (fun p : ℂ × ℂ => (3:ℂ)*(∫ s:ℝ in (0)..1, (s:ℂ)^2*deriv X (p.1+p.2/2*(1-(s:ℂ)^2))))
  exact continuous_const.mul hh
set_option maxHeartbeats 600000 in
lemma barH_joint_continuous : Continuous (fun p : Icc (0:ℝ) y₀ × ℂ => barH (p.1:ℝ) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hpe : (p.1:ℝ)=y₀
  · apply Metric.continuousAt_iff.mpr
    intro ε hε
    let R : ℝ := ‖p.2‖+1
    have hR : 0<R := by dsimp [R]; positivity
    obtain ⟨δY,hδY,hYbound⟩ := Metric.mem_nhdsWithin_iff.mp (critical_normalized_kernels_uniform R hR (ε/2) (by positivity))
    have hg : ContinuousAt (fun w:ℂ => 1-(3/5:ℂ)*w) p.2 := by fun_prop
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
    have happrox : ‖barH (q.1:ℝ) q.2-(1-(3/5:ℂ)*q.2)‖≤ε/2 := by
      by_cases heq : (q.1:ℝ)=y₀
      · simp only [barH,if_pos heq,sub_self,norm_zero]
        positivity
      · exact (hYbound ⟨hdY,lt_of_le_of_ne q.1.property.2 heq⟩ q.2 hqR).2
    have htri := norm_sub_le_norm_sub_add_norm_sub (barH (q.1:ℝ) q.2) (1-(3/5:ℂ)*q.2) (1-(3/5:ℂ)*p.2)
    rw [dist_eq_norm] at hlin ⊢
    rw [show barH (p.1:ℝ) p.2 = 1-(3/5:ℂ)*p.2 by simp [barH,hpe]]
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
    have hn : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => H (q.1:ℝ) ((r (q.1:ℝ):ℂ)*q.2)) p :=
      H_joint_continuous.continuousAt.comp (f := fun q : Icc (0:ℝ) y₀ × ℂ => (((q.1:ℝ):ℂ),(r (q.1:ℝ):ℂ)*q.2)) hpair
    have had : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => (a (q.1:ℝ):ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp (a_continuous.continuousAt.comp (continuous_subtype_val.continuousAt.comp continuous_fst.continuousAt))
    have hc : ContinuousAt (fun q : Icc (0:ℝ) y₀ × ℂ => H (q.1:ℝ) ((r (q.1:ℝ):ℂ)*q.2)/(a (q.1:ℝ):ℂ)) p :=
      hn.div had (by exact_mod_cast a_ne_zero p.1 hpI)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hlt] with q hq
    simp only [barH,if_neg (ne_of_lt hq)]
lemma barH_zero_free_unit (Y:ℝ)(hY:Y∈Icc 0 y₀)(w:ℂ)(hw:‖w‖≤1) : barH Y w≠0 := by
  by_cases he : Y=y₀
  · simp only [barH,if_pos he]
    intro hh
    have hn : ‖(3/5:ℂ)*w‖=1 := by rw [show (3/5:ℂ)*w=1 by linear_combination -hh]; norm_num
    rw [norm_mul] at hn
    norm_num at hn
    nlinarith
  · have hYi : Y∈Ico 0 y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
    simp only [barH,if_neg he]
    apply div_ne_zero
    · apply H_zero_free_closed_disk Y hYi
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (r_pos Y hYi)]
      nlinarith [r_pos Y hYi]
    · exact_mod_cast a_ne_zero Y hYi
lemma barH_uniform_zero_free : ∃ η:ℝ,0<η ∧ ∀ Y∈Icc (0:ℝ) y₀, ∀ w:ℂ, ‖w‖≤1+η → barH Y w≠0 := by
  let S : Set (Icc (0:ℝ) y₀ × ℂ) := univ ×ˢ Metric.closedBall 0 1
  have hS : IsCompact S := isCompact_univ.prod (isCompact_closedBall 0 1)
  let U : Set (Icc (0:ℝ) y₀ × ℂ) := {p | barH (p.1:ℝ) p.2≠0}
  have hU : IsOpen U := isOpen_ne_fun barH_joint_continuous continuous_const
  have hSU : S⊆U := by
    intro p hp
    exact barH_zero_free_unit p.1 p.1.property p.2 (by simpa only [S,mem_prod,mem_univ,mem_closedBall_zero_iff,and_true,true_and] using hp)
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
