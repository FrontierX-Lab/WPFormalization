import WPFormalization.Tight.ConnectedDivergingCoefficients
import WPFormalization.Tight.ConnectedCoefficientScaleTransport
import WPFormalization.Tight.ConnectedScaleTransfer
import WPFormalization.Tight.ConnectedDensityDefinitions
import WPFormalization.Tight.ConnectedPoissonZero
import WPFormalization.Volumes.DiagonalChainAlgebra
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma connected_density_ratio_diverging_large (P:PsiTheory) (k:ℕ) (hk:1≤k) (B:ℝ) (hB:0≤B)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (hgk:∀j,k+3≤gs j) (hn2:∀j,2≤ns j) (ts:ℕ→Fin (2*k)→ℝ)
    (ht:∀j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>connectedDensityCoefficientRatio P k (gs j) (ns j) (ts j)) atTop (𝓝 1) := by
  let xs : ℕ→ℝ := fun j=>connectedSaddle (gs j) (ns j)
  let Ys : ℕ→ℝ := fun j=>inverseY (xs j)
  let Zs : ℕ→ℝ := fun j=>densityY ((ns j:ℝ)/(gs j:ℝ))
  let αs : ℕ→ℝ := fun j=>tightParameterScale (Ys j)
  let αd : ℕ→ℝ := fun j=>tightScale ((ns j:ℝ)/(gs j:ℝ))
  let qs : ℕ→ℝ := fun j=>αs j/αd j
  let vs : ℕ→Fin (2*k)→ℝ := connectedTransportScaledLengths qs ts
  let Ls : ℕ→Fin (2*k)→ℝ := fun j i=>vs j i/αs j
  have hg3 (j:ℕ):3≤gs j := by have:=hgk j;omega
  have hx (j:ℕ):xs j∈Ioo (0:ℝ) xCritical := (connectedSaddle_spec _ _ (by have:=hg3 j;omega) (hn2 j)).1
  have hY (j:ℕ):Ys j∈Ico (0:ℝ) y₀ := (inverseY_branch _ ⟨(hx j).1.le,(hx j).2⟩).1
  have hZ (j:ℕ):Zs j∈Ico (0:ℝ) y₀ := (Analysis.densityY_spec _ (by positivity)).1
  have has (j:ℕ):0<αs j := tightParameterScale_pos _ (hY j)
  have had (j:ℕ):0<αd j := tightScale_pos _ (by positivity)
  have hq : Tendsto qs atTop (𝓝 1) := connectedSaddle_scale_ratio_tendsto gs ns hg hg3 hn2
  have hr0 := connected_r_ratio_tendsto Ys Zs hY hZ hq
  have hr : Tendsto (fun j=>(4*r (Ys j))/(4*r (Zs j))) atTop (𝓝 1) := by
    apply hr0.congr'
    exact Eventually.of_forall (fun j=>by ring)
  have hv : ∀j i,vs j i∈Icc (0:ℝ) (2*B) := connectedTransportScaledLengths_box _ B hB qs ts ht
  have hL : ∀j i,0≤Ls j i ∧ tightParameterScale (inverseY (connectedSaddle (gs j) (ns j)))*Ls j i≤2*B := by
    intro j i
    refine ⟨div_nonneg (hv j i).1 (has j).le,?_⟩
    change αs j*(vs j i/αs j)≤2*B
    rw [mul_div_cancel₀ _ (has j).ne']
    exact (hv j i).2
  have hsrc0 := connected_coefficient_ratio_diverging P k hk (2*B) (by positivity) gs ns hg hn
    (fun j=>by have:=hgk j;omega) hn2 Ls hL
  have hsrc : Tendsto (fun j=>
      realCoeff (TightMoments.momentTightG P (gs j-k) (2*k) (fun i=>vs j i/αs j)) (ns j)/
        (realCoeff (Phi P (gs j)) (ns j)*((4*r (Ys j))^k*∏i,boundaryFactor 0 (vs j i)))) atTop (𝓝 1) := by
    apply hsrc0.congr'
    apply Eventually.of_forall
    intro j
    have he (i:Fin (2*k)) : tightParameterScale (inverseY (connectedSaddle (gs j) (ns j)))*Ls j i=vs j i := by
      change αs j*(vs j i/αs j)=vs j i
      rw [mul_div_cancel₀ _ (has j).ne']
    simp_rw [he]
    change _/((4*r (Ys j))^k*(∏i,boundaryFactor 0 (vs j i))*_)=_
    ring
  exact connected_coefficient_scale_transport k B hB
    (fun j L=>realCoeff (TightMoments.momentTightG P (gs j-k) (2*k) L) (ns j))
    (fun j=>realCoeff (Phi P (gs j)) (ns j)) (fun j=>4*r (Ys j)) (fun j=>4*r (Zs j)) αs αd
    had (Eventually.of_forall has)
    (Eventually.of_forall (fun j=>(mul_pos (by norm_num) (r_pos _ (hY j))).ne'))
    (Eventually.of_forall (fun j=>(mul_pos (by norm_num) (r_pos _ (hZ j))).ne'))
    hq hr ts ht hsrc

lemma connected_density_ratio_diverging_positive (P:PsiTheory) (k:ℕ) (hk:1≤k) (B:ℝ) (hB:0≤B)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (ts:ℕ→Fin (2*k)→ℝ) (ht:∀j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>connectedDensityCoefficientRatio P k (gs j) (ns j) (ts j)) atTop (𝓝 1) := by
  let gs' : ℕ→ℕ := fun j=>max (k+3) (gs j)
  let ns' : ℕ→ℕ := fun j=>max 2 (ns j)
  have hg' : Tendsto gs' atTop atTop := tendsto_atTop_mono (fun j=>le_max_right _ _) hg
  have hn' : Tendsto ns' atTop atTop := tendsto_atTop_mono (fun j=>le_max_right _ _) hn
  have hr := connected_density_ratio_diverging_large P k hk B hB gs' ns' hg' hn'
    (fun j=>le_max_left _ _) (fun j=>le_max_left _ _) ts ht
  apply hr.congr'
  filter_upwards [hg.eventually_ge_atTop (k+3),hn.eventually_ge_atTop 2] with j hj hk
  simp only [gs',ns',max_eq_right hj,max_eq_right hk]

lemma connected_density_ratio_diverging (P:PsiTheory) (k:ℕ) (B:ℝ) (hB:0≤B)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (ts:ℕ→Fin (2*k)→ℝ) (ht:∀j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>connectedDensityCoefficientRatio P k (gs j) (ns j) (ts j)) atTop (𝓝 1) := by
  by_cases hk : k=0
  · subst k
    apply (show Tendsto (fun _j:ℕ=>(1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).congr'
    filter_upwards [hg.eventually_ge_atTop 2,hn.eventually_ge_atTop 1] with j hj hnj
    have hV := diagonal_volume_pos_nonempty P (gs j) (ns j) hnj (by unfold Stable;omega)
    have hcoef : 0<realCoeff (Phi P (gs j)) (ns j) := by
      have he := marked_realCoeff_volume P (gs j) 0 (ns j)
      simp only [iteratedDeriv_zero,Nat.add_zero] at he
      rw [he]
      positivity
    unfold connectedDensityCoefficientRatio
    simp only [Nat.mul_zero,Nat.sub_zero,pow_zero,Fin.prod_univ_zero,mul_one]
    rw [connected_momentTightG_zero_coeff P (gs j) hj _ (ns j),div_self hcoef.ne']
  · exact connected_density_ratio_diverging_positive P k (by omega) B hB gs ns hg hn ts ht
end WP.TightConnected
