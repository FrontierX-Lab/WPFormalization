import WPFormalization.Tight.ConnectedScale
import WPFormalization.Tight.ConnectedVariance
import WPFormalization.Marked.LogGrowth
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma connected_standardized_unit_bound (h x : ℝ) (hh : 0<h)
    (hx : x∈Ioo (0:ℝ) xCritical) :
    (1+Psi x)/Real.sqrt (h*euler Psi x) ≤ 4/Real.sqrt (min h (h*Psi x)) := by
  have hp := (connected_variance_formula x hx).1
  have hv : 0<euler Psi x := hp.trans_le (BoundaryConvolution.boundary_variance_ge_mean x hx)
  have hm : 0 < min h (h*Psi x) := lt_min hh (mul_pos hh hp)
  have hsm := Real.sqrt_pos.mpr hm
  have hσ := Real.sqrt_pos.mpr (mul_pos hh hv)
  have hscale : Real.sqrt (min h (h*Psi x))*(1+Psi x)≤4*Real.sqrt (h*euler Psi x) := by
    have hs := connected_variance_scale_bound h x hh hx
    have hsq := Real.sq_sqrt hm.le
    have hσsq := Real.sq_sqrt (mul_pos hh hv).le
    have hleft : 0≤Real.sqrt (min h (h*Psi x))*(1+Psi x) := by positivity
    nlinarith [sq_nonneg (Real.sqrt (min h (h*Psi x))*(1+Psi x)-4*Real.sqrt (h*euler Psi x))]
  apply (div_le_div_iff₀ hσ hsm).mpr
  nlinarith

lemma connected_standardized_unit_tendsto (hs xs : ℕ→ℝ)
    (hh : ∀j,0<hs j) (hx : ∀j,xs j∈Ioo (0:ℝ) xCritical)
    (hhs : Tendsto hs atTop atTop)
    (hmean : Tendsto (fun j=>hs j*Psi (xs j)) atTop atTop) :
    Tendsto (fun j=>(1+Psi (xs j))/Real.sqrt (hs j*euler Psi (xs j))) atTop (𝓝 0) := by
  have hm : Tendsto (fun j=>min (hs j) (hs j*Psi (xs j))) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hhs.eventually_ge_atTop b,hmean.eventually_ge_atTop b] with j hj hk
    exact le_min hj hk
  have hbound := (Real.tendsto_sqrt_atTop.comp hm).const_div_atTop (4:ℝ)
  apply squeeze_zero' (Eventually.of_forall (fun j=>by
    exact div_nonneg (by linarith [(connected_variance_formula _ (hx j)).1]) (Real.sqrt_nonneg _))) _ hbound
  exact Eventually.of_forall (fun j=>connected_standardized_unit_bound (hs j) (xs j) (hh j) (hx j))

lemma connectedSaddle_numerator_mean_tendsto (gs ns : ℕ→ℕ)
    (hg2 : ∀j,2≤gs j) (hn2 : ∀j,2≤ns j) (hn : Tendsto ns atTop atTop) :
    Tendsto (fun j=>(complexity (gs j) 0:ℝ)*Psi (connectedSaddle (gs j) (ns j))) atTop atTop := by
  have hnR : Tendsto (fun j=>(ns j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  apply tendsto_atTop.2
  intro b
  filter_upwards [hnR.eventually_ge_atTop (2*b+1)] with j hj
  have hs := connectedSaddle_spec (gs j) (ns j) (hg2 j) (hn2 j)
  have hp := (connected_variance_formula _ hs.1).1
  have hhc : (complexity (gs j) 1:ℝ)=(complexity (gs j) 0:ℝ)+1 := by
    exact_mod_cast (show complexity (gs j) 1=complexity (gs j) 0+1 by unfold complexity;have:=hg2 j;omega)
  have hh : 1≤(complexity (gs j) 0:ℝ) := by
    exact_mod_cast (show 1≤complexity (gs j) 0 by unfold complexity;have:=hg2 j;omega)
  have hm := hs.2.1
  rw [hhc] at hm
  nlinarith [mul_nonneg (by linarith : 0≤(complexity (gs j) 0:ℝ)-1) hp.le]

lemma connectedSaddle_offset_tendsto (gs ns : ℕ→ℕ)
    (hg : Tendsto gs atTop atTop) (hn : Tendsto ns atTop atTop)
    (hg2 : ∀j,2≤gs j) (hn2 : ∀j,2≤ns j) :
    Tendsto (fun j=>((ns j:ℝ)-(complexity (gs j) 0:ℝ)*Psi (connectedSaddle (gs j) (ns j)))/
      Real.sqrt ((complexity (gs j) 0:ℝ)*euler Psi (connectedSaddle (gs j) (ns j)))) atTop (𝓝 0) := by
  have hs (j:ℕ) := connectedSaddle_spec (gs j) (ns j) (hg2 j) (hn2 j)
  have ht := connected_standardized_unit_tendsto (fun j=>(complexity (gs j) 0:ℝ))
    (fun j=>connectedSaddle (gs j) (ns j))
    (fun j=>by exact_mod_cast (show 0<complexity (gs j) 0 by unfold complexity;have:=hg2 j;omega))
    (fun j=>(hs j).1) ((Analysis.complexity_real_tendsto_atTop 0).comp hg)
    (connectedSaddle_numerator_mean_tendsto gs ns hg2 hn2 hn)
  apply ht.congr'
  apply Eventually.of_forall
  intro j
  dsimp only
  congr 1
  have hhc : (complexity (gs j) 1:ℝ)=(complexity (gs j) 0:ℝ)+1 := by
    exact_mod_cast (show complexity (gs j) 1=complexity (gs j) 0+1 by unfold complexity;have:=hg2 j;omega)
  have hm := (hs j).2.1
  rw [hhc] at hm
  nlinarith
end WP.TightConnected
