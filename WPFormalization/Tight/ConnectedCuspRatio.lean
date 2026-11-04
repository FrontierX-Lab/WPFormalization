import WPFormalization.Tight.ConnectedGenusRatio
import WPFormalization.Tight.ConnectedScale
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology
lemma connected_marked_leading_relative_tendsto (P:PsiTheory) (p:ℕ)
    (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (Ys:ℕ→ℝ) (hY:∀j,Ys j∈Ico 0 y₀) :
    Tendsto (fun j=>Real.pi*markedF P (gs j) p (XR (Ys j))/markedModel (gs j) p (Ys j)) atTop (𝓝 1) := by
  obtain ⟨C,hC,G,hbound⟩ := connected_marked_leading_relative_error P p
  have he : Tendsto (fun j=>Real.pi*markedF P (gs j) p (XR (Ys j))/markedModel (gs j) p (Ys j)-1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ((tendsto_natCast_atTop_atTop.comp hg).const_div_atTop C)
    filter_upwards [hg.eventually_ge_atTop G] with j hj
    simpa only [Real.norm_eq_abs,Function.comp_def] using hbound (gs j) hj (Ys j) (hY j)
  simpa only [zero_add,sub_add_cancel] using he.add_const 1

lemma connected_complexity_ratio_tendsto (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop)
    (hg2:∀j,2≤gs j) :
    Tendsto (fun j=>(complexity (gs j) 0:ℝ)/(complexity (gs j) 1:ℝ)) atTop (𝓝 1) := by
  have h1 := (Analysis.complexity_real_tendsto_atTop 1).comp hg
  have ht : Tendsto (fun j=>(1:ℝ)-1/(complexity (gs j) 1:ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero,Function.comp_def] using
      (show Tendsto (fun _j:ℕ=>(1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub
        (h1.const_div_atTop (1:ℝ))
  apply ht.congr'
  exact Eventually.of_forall (fun j=>by
    have hh : (complexity (gs j) 1:ℝ)=(complexity (gs j) 0:ℝ)+1 := by
      exact_mod_cast (show complexity (gs j) 1=complexity (gs j) 0+1 by unfold complexity;have:=hg2 j;omega)
    have hh0 : 0<(complexity (gs j) 1:ℝ) := by exact_mod_cast (show 0<complexity (gs j) 1 by unfold complexity;have:=hg2 j;omega)
    dsimp only
    field_simp
    linarith)

/-- The actual unmarked cusp ratio, uniform along arbitrary physical weights.
It is derived from the original leading prefactors, not assumed at p=0. -/
lemma connected_unmarked_cusp_ratio_tendsto (P:PsiTheory)
    (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hg2:∀j,2≤gs j)
    (xs:ℕ→ℝ) (hx:∀j,xs j∈Ioo (0:ℝ) xCritical) :
    Tendsto (fun j=>xs j*markedF P (gs j) 1 (xs j)/
      ((complexity (gs j) 1:ℝ)*Psi (xs j)*markedF P (gs j) 0 (xs j))) atTop (𝓝 1) := by
  let Ys : ℕ→ℝ := fun j=>inverseY (xs j)
  have hY (j:ℕ) : Ys j∈Ico (0:ℝ) y₀ := (inverseY_branch _ ⟨(hx j).1.le,(hx j).2⟩).1
  have hXY (j:ℕ) : XR (Ys j)=xs j := (inverseY_branch _ ⟨(hx j).1.le,(hx j).2⟩).2
  have ha0 := connected_marked_leading_relative_tendsto P 0 gs hg Ys hY
  have ha1 := connected_marked_leading_relative_tendsto P 1 gs hg Ys hY
  have hq := connected_complexity_ratio_tendsto gs hg hg2
  have hsqrt : Tendsto (fun j=>Real.sqrt ((complexity (gs j) 0:ℝ)/(complexity (gs j) 1:ℝ))) atTop (𝓝 1) := by
    simpa only [Real.sqrt_one,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hq
  have ht := ((ha1.div ha0 (by norm_num)).mul hq).mul hsqrt
  simp only [one_div,inv_one,one_mul] at ht
  apply ht.congr'
  filter_upwards [ha0.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1))] with j hj
  have hs : Stable (gs j) 0 := by unfold Stable;have:=hg2 j;omega
  have hF : markedF P (gs j) 0 (xs j)≠0 := by
    intro hz
    rw [hXY j,hz,mul_zero,zero_div] at hj
    linarith
  have hM : markedModel (gs j) 0 (Ys j)≠0 := (markedModel_pos_parameter _ _ hs _ (hY j)).ne'
  have hc0 : (complexity (gs j) 0:ℝ)≠0 := by
    have hh : 0<(complexity (gs j) 0:ℝ) := by exact_mod_cast (show 0<complexity (gs j) 0 by unfold complexity;have:=hg2 j;omega)
    exact hh.ne'
  have hc1 : (complexity (gs j) 1:ℝ)≠0 := by
    have hh : 0<(complexity (gs j) 1:ℝ) := by exact_mod_cast (show 0<complexity (gs j) 1 by unfold complexity;have:=hg2 j;omega)
    exact hh.ne'
  have hA := Analysis.marked_A_pos (Ys j) ⟨(hY j).1,(hY j).2.le⟩
  have ha := a_pos _ (hY j)
  have hr := r_pos _ (hY j)
  have hX := (hx j).1.ne'
  have hc : (complexity (gs j) 0+1:ℕ)=complexity (gs j) 1 := by unfold complexity;have:=hg2 j;omega
  simp only [Pi.div_apply]
  rw [Analysis.ratioModel_cusp_identity (gs j) 0 hs (Ys j) (hY j)]
  norm_num only [Nat.zero_add]
  rw [hc]
  simp_rw [hXY j]
  rw [←hXY j,Psi_XR_eq_kernel_ratio _ (hY j),hXY j]
  field_simp [hM,hF,hc0,hc1,hA.ne',ha.ne',hr.ne',hX,Real.pi_ne_zero]
  <;>ring

lemma connectedSaddle_cusp_prefactor_tendsto (P:PsiTheory)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (hg2:∀j,2≤gs j) (hn2:∀j,2≤ns j) :
    Tendsto (fun j=>(ns j:ℝ)*markedF P (gs j) 0 (connectedSaddle (gs j) (ns j))/
      (connectedSaddle (gs j) (ns j)*markedF P (gs j) 1 (connectedSaddle (gs j) (ns j)))) atTop (𝓝 1) := by
  let xs : ℕ→ℝ := fun j=>connectedSaddle (gs j) (ns j)
  have hs (j:ℕ) := connectedSaddle_spec (gs j) (ns j) (hg2 j) (hn2 j)
  have hcusp := connected_unmarked_cusp_ratio_tendsto P gs hg hg2 xs (fun j=>(hs j).1)
  have hnR : Tendsto (fun j=>(ns j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hqT : Tendsto (fun j=>(ns j:ℝ)-1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hnR.eventually_ge_atTop (b+1)] with j hj
    linarith
  have hnratio : Tendsto (fun j=>(ns j:ℝ)/((ns j:ℝ)-1)) atTop (𝓝 1) := by
    have ht : Tendsto (fun j=>(1:ℝ)+1/((ns j:ℝ)-1)) atTop (𝓝 1) := by
      simpa only [add_zero] using
        (show Tendsto (fun _j:ℕ=>(1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).add
          (hqT.const_div_atTop (1:ℝ))
    apply ht.congr'
    exact Eventually.of_forall (fun j=>by
      have hh : ((ns j:ℝ)-1)≠0 := by
        have hn2R : (2:ℝ)≤ns j := by exact_mod_cast hn2 j
        linarith
      dsimp only
      field_simp
      <;>ring)
  have ht := hnratio.div hcusp (by norm_num)
  simp only [div_self (by norm_num : (1:ℝ)≠0)] at ht
  apply ht.congr'
  filter_upwards [hcusp.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1))] with j hj
  have hF0 : markedF P (gs j) 0 (xs j)≠0 := by
    intro hz
    rw [hz,mul_zero,div_zero] at hj
    linarith
  have hF1 : markedF P (gs j) 1 (xs j)≠0 :=
    (markedF_positive_cusp_weight P (gs j) 1 (by omega) (by unfold Stable;have:=hg2 j;omega)
      (xs j) ⟨(hs j).1.1.le,(hs j).1.2⟩).ne'
  have hx : xs j≠0 := (hs j).1.1.ne'
  have hn0 : ((ns j:ℝ)-1)≠0 := by
    have hn2R : (2:ℝ)≤ns j := by exact_mod_cast hn2 j
    linarith
  simp only [Pi.div_apply]
  rw [(hs j).2.1]
  dsimp [xs]
  field_simp [hF0,hF1,hx,hn0]
  <;>ring
end WP.TightConnected
