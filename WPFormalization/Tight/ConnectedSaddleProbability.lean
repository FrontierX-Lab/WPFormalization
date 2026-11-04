import WPFormalization.Tight.ConnectedCutLocalLimit
import WPFormalization.Tight.ConnectedCuspRatio
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma connected_variance_ratio_tendsto (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop)
    (hg2:∀j,2≤gs j) (xs:ℕ→ℝ) (hx:∀j,xs j∈Ioo (0:ℝ) xCritical) :
    Tendsto (fun j=>Real.sqrt ((complexity (gs j) 0:ℝ)*euler Psi (xs j))/
      Real.sqrt ((complexity (gs j) 1:ℝ)*euler Psi (xs j))) atTop (𝓝 1) := by
  have hq := connected_complexity_ratio_tendsto gs hg hg2
  have ht : Tendsto (fun j=>Real.sqrt ((complexity (gs j) 0:ℝ)/(complexity (gs j) 1:ℝ))) atTop (𝓝 1) := by
    simpa only [Real.sqrt_one,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hq
  apply ht.congr'
  exact Eventually.of_forall (fun j=>by
    have h0 : 0<(complexity (gs j) 0:ℝ) := by exact_mod_cast (show 0<complexity (gs j) 0 by unfold complexity;have:=hg2 j;omega)
    have h1 : 0<(complexity (gs j) 1:ℝ) := by exact_mod_cast (show 0<complexity (gs j) 1 by unfold complexity;have:=hg2 j;omega)
    have hp := (connected_variance_formula _ (hx j)).1
    have hv : 0<euler Psi (xs j) := hp.trans_le (BoundaryConvolution.boundary_variance_ge_mean _ (hx j))
    dsimp only
    rw [←Real.sqrt_div (mul_pos h0 hv).le]
    congr 1
    field_simp)

lemma connectedSaddle_probability_ratio_tendsto (P:PsiTheory) (k:ℕ) (hk:1≤k) (B:ℝ) (hB:0≤B)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (hgk:∀j,k+2≤gs j) (hn2:∀j,2≤ns j) (Ls:ℕ→Fin (2*k)→ℝ)
    (hL:∀j i,0≤Ls j i ∧ tightParameterScale (inverseY (connectedSaddle (gs j) (ns j)))*Ls j i≤B) :
    Tendsto (fun j=>tightMass P (gs j-k) (2*k) (Ls j) (ns j) (connectedSaddle (gs j) (ns j))/
      cuspMass P (gs j) 1 (ns j-1) (connectedSaddle (gs j) (ns j))) atTop (𝓝 1) := by
  have hg2 (j:ℕ):2≤gs j := by have:=hgk j;omega
  have hnumer := connectedSaddle_numerator_scaled_limit P k hk B hB gs ns hg hn hgk hn2 Ls hL
  have hdenom := connectedSaddle_denominator_scaled_limit P gs ns hg hn hg2 hn2
  have hvar := connected_variance_ratio_tendsto gs hg hg2
    (fun j=>connectedSaddle (gs j) (ns j)) (fun j=>(connectedSaddle_spec _ _ (hg2 j) (hn2 j)).1)
  have hc : (1/Real.sqrt (2*Real.pi))≠0 := by positivity
  have ht := (hnumer.div hdenom hc).div hvar (by norm_num)
  simp only [div_self hc,div_self (by norm_num : (1:ℝ)≠0)] at ht
  apply ht.congr'
  filter_upwards [connectedSaddle_denominator_positive_lower P gs ns hg hn hg2 hn2] with j hj
  have hp := (connected_variance_formula _ (connectedSaddle_spec _ _ (hg2 j) (hn2 j)).1).1
  have hv : 0<euler Psi (connectedSaddle (gs j) (ns j)) := hp.trans_le
    (BoundaryConvolution.boundary_variance_ge_mean _ (connectedSaddle_spec _ _ (hg2 j) (hn2 j)).1)
  have h0 : 0<(complexity (gs j) 0:ℝ) := by exact_mod_cast (show 0<complexity (gs j) 0 by unfold complexity;have:=hg2 j;omega)
  have h1 : 0<(complexity (gs j) 1:ℝ) := by exact_mod_cast (show 0<complexity (gs j) 1 by unfold complexity;have:=hg2 j;omega)
  have hs0 : Real.sqrt ((complexity (gs j) 0:ℝ)*euler Psi (connectedSaddle (gs j) (ns j)))≠0 :=
    (Real.sqrt_pos.mpr (mul_pos h0 hv)).ne'
  have hs1 : Real.sqrt ((complexity (gs j) 1:ℝ)*euler Psi (connectedSaddle (gs j) (ns j)))≠0 :=
    (Real.sqrt_pos.mpr (mul_pos h1 hv)).ne'
  have hmass : cuspMass P (gs j) 1 (ns j-1) (connectedSaddle (gs j) (ns j))≠0 := by
    intro hz
    rw [hz,mul_zero] at hj
    have hcpos : 0<1/(2*Real.sqrt (2*Real.pi)) := by positivity
    linarith
  simp only [Pi.div_apply]
  field_simp [hs0,hs1,hmass]
end WP.TightConnected
