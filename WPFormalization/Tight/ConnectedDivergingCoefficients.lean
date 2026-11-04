import WPFormalization.Tight.ConnectedSaddleProbability
import WPFormalization.Tight.ConnectedCoefficientAlgebra
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology
lemma tight_real_axis_ratio_tendsto (P:PsiTheory) (p:ℕ) (hp:1≤p) (B:ℝ) (hB:0≤B)
    (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (xs:ℕ→ℝ)
    (hx:∀j,xs j∈Ioo (0:ℝ) xCritical) (Ls:ℕ→Fin p→ℝ)
    (hL:∀j i,0≤Ls j i ∧ tightParameterScale (inverseY (xs j))*Ls j i≤B) :
    Tendsto (fun j=>(TightMoments.momentTightG P (gs j) p (Ls j) (xs j:ℂ)).re/
      (markedF P (gs j) p (xs j)*∏i,boundaryFactor 0 (tightParameterScale (inverseY (xs j))*Ls j i))) atTop (𝓝 1) := by
  obtain ⟨C,hC,hbound⟩ := tightShiftedPolynomial_uniform_relative_error P p hp B hB
  have herror : Tendsto (fun j=>C/(gs j:ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hg).const_div_atTop C
  have ht : Tendsto (fun j=>(TightMoments.momentTightG P (gs j) p (Ls j) (xs j:ℂ)).re/
      (markedF P (gs j) p (xs j)*∏i,boundaryFactor 0 (tightParameterScale (inverseY (xs j))*Ls j i))-1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ herror
    filter_upwards [hg.eventually_ge_atTop 2] with j hj
    have hs : Stable (gs j) p := by unfold Stable;omega
    have he := hbound (gs j) (by omega) (inverseY (xs j)) (inverseY_branch _ ⟨(hx j).1.le,(hx j).2⟩).1
      (Ls j) (fun i=>(hL j i).1) (fun i=>(hL j i).2)
    have hshift := string_flow_proof P (gs j) p hs (inverseY (xs j))
      (inverseY_branch _ ⟨(hx j).1.le,(hx j).2⟩).1
    rw [(inverseY_branch _ ⟨(hx j).1.le,(hx j).2⟩).2] at hshift
    rw [hshift] at he
    rw [TightMoments.momentTightG_ofReal P (gs j) p (Ls j) (xs j) ⟨(hx j).1.le,(hx j).2⟩,Complex.ofReal_re]
    simpa only [Real.norm_eq_abs] using he
  simpa only [sub_add_cancel,zero_add] using ht.add_const 1

/-- The original connected-cut coefficient asymptotic in the n->infinity
branch, uniformly along arbitrary sequences of scaled lengths in a fixed box. -/
lemma connected_coefficient_ratio_diverging (P:PsiTheory) (k:ℕ) (hk:1≤k) (B:ℝ) (hB:0≤B)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (hgk:∀j,k+2≤gs j) (hn2:∀j,2≤ns j) (Ls:ℕ→Fin (2*k)→ℝ)
    (hL:∀j i,0≤Ls j i ∧ tightParameterScale (inverseY (connectedSaddle (gs j) (ns j)))*Ls j i≤B) :
    Tendsto (fun j=>realCoeff (TightMoments.momentTightG P (gs j-k) (2*k) (Ls j)) (ns j)/
      ((4*r (inverseY (connectedSaddle (gs j) (ns j))))^k*
        (∏i,boundaryFactor 0 (tightParameterScale (inverseY (connectedSaddle (gs j) (ns j)))*Ls j i))*
        realCoeff (Phi P (gs j)) (ns j))) atTop (𝓝 1) := by
  let xs : ℕ→ℝ := fun j=>connectedSaddle (gs j) (ns j)
  have hg2 (j:ℕ):2≤gs j := by have:=hgk j;omega
  have hx (j:ℕ):xs j∈Ioo (0:ℝ) xCritical := (connectedSaddle_spec _ _ (hg2 j) (hn2 j)).1
  have hY (j:ℕ):inverseY (xs j)∈Ico (0:ℝ) y₀ := (inverseY_branch _ ⟨(hx j).1.le,(hx j).2⟩).1
  have hX (j:ℕ):XR (inverseY (xs j))=xs j := (inverseY_branch _ ⟨(hx j).1.le,(hx j).2⟩).2
  have hpre := connectedSaddle_cusp_prefactor_tendsto P gs ns hg hn hg2 hn2
  have haxis := tight_real_axis_ratio_tendsto P (2*k) (by omega) B hB (fun j=>gs j-k)
    (connected_nat_sub_tendsto gs hg k) xs hx Ls hL
  have hgen := connected_fixed_genus_ratio_tendsto P k gs hg (fun j=>inverseY (xs j)) hY
  have hprob := connectedSaddle_probability_ratio_tendsto P k hk B hB gs ns hg hn hgk hn2 Ls hL
  have ht := ((hpre.mul haxis).mul hgen).mul hprob
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [hpre.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1)),
    connectedSaddle_denominator_positive_lower P gs ns hg hn hg2 hn2] with j hj hden
  have hs0 : Stable (gs j) 1 := by unfold Stable;have:=hg2 j;omega
  have hsn : Stable (gs j-k) (2*k) := by unfold Stable;have:=hgk j;omega
  have hF : markedF P (gs j-k) (2*k) (xs j)≠0 :=
    (markedF_positive_cusp_weight P _ _ (by omega) hsn _ ⟨(hx j).1.le,(hx j).2⟩).ne'
  have hF1 : markedF P (gs j) 1 (xs j)≠0 :=
    (markedF_positive_cusp_weight P _ _ (by omega) hs0 _ ⟨(hx j).1.le,(hx j).2⟩).ne'
  have hF0 : markedF P (gs j) 0 (xs j)≠0 := by
    intro hz
    change 0<(ns j:ℝ)*markedF P (gs j) 0 (xs j)/(xs j*markedF P (gs j) 1 (xs j)) at hj
    rw [hz,mul_zero,zero_div] at hj
    linarith
  have hmass : cuspMass P (gs j) 1 (ns j-1) (xs j)≠0 := by
    intro hz
    change _≤Real.sqrt ((complexity (gs j) 1:ℝ)*euler Psi (xs j))*cuspMass P (gs j) 1 (ns j-1) (xs j) at hden
    rw [hz,mul_zero] at hden
    have hc : 0<1/(2*Real.sqrt (2*Real.pi)) := by positivity
    linarith
  have he := connected_coefficient_ratio_mass_identity P (gs j) (gs j-k) (2*k) (by omega)
    hs0 hsn (Ls j) (ns j) (by have:=hn2 j;omega) (xs j) (hx j) hmass
  have hb : (∏i,boundaryFactor 0 (tightParameterScale (inverseY (xs j))*Ls j i))≠0 :=
    (Finset.prod_pos (fun i _=>boundaryFactor_pos _ _)).ne'
  have hr : r (inverseY (xs j))≠0 := (r_pos _ (hY j)).ne'
  have hcoef : realCoeff (Phi P (gs j)) (ns j)≠0 := by
    intro hz
    apply hmass
    unfold cuspMass
    have hc : realCoeff (iteratedDeriv 1 (Phi P (gs j))) (ns j-1)=
        (ns j:ℝ)*realCoeff (Phi P (gs j)) (ns j) := by
      rw [iteratedDeriv_one,connected_realCoeff_deriv]
      have hncast : ((ns j-1:ℕ):ℝ)+1=(ns j:ℝ) := by exact_mod_cast (show ns j-1+1=ns j by have:=hn2 j;omega)
      rw [show ns j-1+1=ns j by have:=hn2 j;omega,hncast]
    rw [hc,hz,mul_zero,zero_mul,zero_div]
  simp_rw [hX j]
  have htarget : realCoeff (TightMoments.momentTightG P (gs j-k) (2*k) (Ls j)) (ns j)/
      ((4*r (inverseY (xs j)))^k*(∏i,boundaryFactor 0 (tightParameterScale (inverseY (xs j))*Ls j i))*
        realCoeff (Phi P (gs j)) (ns j))=
      (realCoeff (TightMoments.momentTightG P (gs j-k) (2*k) (Ls j)) (ns j)/
        realCoeff (Phi P (gs j)) (ns j))/
        ((4*r (inverseY (xs j)))^k*(∏i,boundaryFactor 0 (tightParameterScale (inverseY (xs j))*Ls j i))) := by ring
  change _=realCoeff (TightMoments.momentTightG P (gs j-k) (2*k) (Ls j)) (ns j)/
    ((4*r (inverseY (xs j)))^k*(∏i,boundaryFactor 0 (tightParameterScale (inverseY (xs j))*Ls j i))*realCoeff (Phi P (gs j)) (ns j))
  rw [htarget,he]
  dsimp only [xs] at hF hF1 hF0 hmass hb hr hcoef ⊢
  field_simp [hF,hF1,hF0,hmass,hb,hr,hcoef,(hx j).1.ne']
  <;>ring
end WP.TightConnected
