import WPFormalization.Tight.ConnectedPoissonTight
import WPFormalization.Tight.ConnectedPoissonZero

noncomputable section
namespace WP.TightConnected
open Set Filter TightMoments
open scoped Topology

lemma connected_cut_genus_tendsto (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop) (k : ℕ) :
    Tendsto (fun j=>gs j-k) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [hg.eventually_ge_atTop (N+k)] with j hj
  omega

lemma connected_cut_complexity_ratio (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop) (k : ℕ) :
    Tendsto (fun j=>(complexity (gs j-k) (2*k):ℝ)/(complexity (gs j) 0:ℝ))
      atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hg.eventually_ge_atTop (k+2)] with j hj
  have he : complexity (gs j-k) (2*k)=complexity (gs j) 0 := by unfold complexity;omega
  have hp : 0<(complexity (gs j) 0:ℝ) := by
    exact_mod_cast (show 0<complexity (gs j) 0 by unfold complexity;omega)
  exact (by rw [he,div_self hp.ne'])

lemma connected_fixed_genus_ratio_tendsto_eventual (P : PsiTheory) (k : ℕ)
    (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop) (xs : ℕ→ℝ)
    (hx : ∀ᶠ j in atTop,xs j∈Ico (0:ℝ) xCritical) :
    Tendsto (fun j=>markedF P (gs j-k) (2*k) (xs j)/
      ((4*r (inverseY (xs j)))^k*markedF P (gs j) 0 (xs j))) atTop (𝓝 1) := by
  let Ys : ℕ→ℝ := fun j=>if xs j∈Ico (0:ℝ) xCritical then inverseY (xs j) else 0
  have hY : ∀ j,Ys j∈Ico (0:ℝ) y₀ := by
    intro j
    by_cases hj:xs j∈Ico (0:ℝ) xCritical
    · simpa only [Ys,ite_eq_left hj] using (inverseY_branch _ hj).1
    · simpa only [Ys,ite_eq_right hj] using (show (0:ℝ)∈Ico (0:ℝ) y₀ from ⟨le_rfl,y₀_pos⟩)
  have ht := connected_fixed_genus_ratio_tendsto P k gs hg Ys hY
  apply ht.congr'
  filter_upwards [hx] with j hj
  simp only [Ys,ite_eq_left hj,(inverseY_branch _ hj).2]

lemma connected_coefficient_ratio_bounded_positive_cuts (P : PsiTheory) (k n : ℕ) (hk : 1≤k)
    (c : ℝ) (hc : 0<c) (B : ℝ) (hB : 0≤B)
    (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop)
    (ts : ℕ→Fin (2*k)→ℝ) (ht : ∀ j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>realCoeff (momentTightG P (gs j-k) (2*k)
      (fun i=>ts j i/tightParameterScale (inverseY (c/(complexity (gs j) 0:ℝ))))) n /
        (realCoeff (Phi P (gs j)) n *
          ((4*r (inverseY (c/(complexity (gs j) 0:ℝ))))^k *
            ∏ i,boundaryFactor 0 (ts j i)))) atTop (𝓝 1) := by
  let hs : ℕ→ℝ := fun j=>(complexity (gs j) 0:ℝ)
  let xs : ℕ→ℝ := fun j=>c/hs j
  let Ls : ℕ→Fin (2*k)→ℝ := fun j i=>ts j i/tightParameterScale (inverseY (xs j))
  let R : ℕ→ℝ := fun j=>(4*r (inverseY (xs j)))^k
  let S : ℕ→ℝ := fun j=>∏ i,boundaryFactor 0 (ts j i)
  have hh : Tendsto hs atTop atTop := connected_complexity_tendsto gs hg
  have hgc := connected_cut_genus_tendsto gs hg k
  have hch := connected_cut_complexity_ratio gs hg k
  have hx : ∀ᶠ j in atTop,xs j∈Ico (0:ℝ) xCritical := connected_small_weight_eventually hs hh c hc.le
  have hnorm := connected_tight_poisson_normalization P (2*k) (by omega) _ hgc hs hh c hc B hB ts ht c hc.le
  have hgenus := connected_fixed_genus_ratio_tendsto_eventual P k gs hg xs hx
  have hvalue : Tendsto (fun j=>(momentTightG P (gs j-k) (2*k) (Ls j) (xs j:ℂ)).re /
      (markedF P (gs j) 0 (xs j)*R j*S j)) atTop (𝓝 1) := by
    have hlimit := hnorm.mul hgenus
    simp only [one_mul] at hlimit
    apply hlimit.congr'
    filter_upwards [hg.eventually_ge_atTop (k+2),hx] with j hj hxj
    have hF : markedF P (gs j-k) (2*k) (xs j) ≠ 0 :=
      (markedF_positive_cusp_weight P _ _ (by omega) (by unfold Stable;omega) _ hxj).ne'
    change ((momentTightG P (gs j-k) (2*k) (Ls j) (xs j:ℂ)).re /
      (markedF P (gs j-k) (2*k) (xs j)*S j)) *
        (markedF P (gs j-k) (2*k) (xs j)/(R j*markedF P (gs j) 0 (xs j))) = _
    field_simp
  have hn := connected_tight_poisson_probability_limit P (2*k) (by omega) _ hgc hs hh hch c hc B hB ts ht n
  have hd := connected_phi_poisson_probability_limit P n c hc gs hg
  have hp : 0<Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ) := by positivity
  have hprob := hn.div hd hp.ne'
  simp only [div_self hp.ne'] at hprob
  have hlimit := hprob.mul hvalue
  simp only [one_mul] at hlimit
  obtain ⟨G,hG⟩ := connected_unmarked_positive_eventually P
  apply hlimit.congr'
  filter_upwards [hg.eventually_ge_atTop (G+k+2),hx,hh.eventually_gt_atTop 0,
    hd.eventually_ne hp.ne'] with j hj hxj hhj hden
  have hPhi : markedF P (gs j) 0 (xs j)≠0 := (hG _ (by omega) _ hxj).ne'
  have hCut : (momentTightG P (gs j-k) (2*k) (Ls j) (xs j:ℂ)).re≠0 :=
    (momentTightG_real_pos P _ _ (by omega) (by unfold Stable;omega) _ _ hxj).ne'
  have hCoeff : realCoeff (Phi P (gs j)) n≠0 := by
    intro he
    simp only [he,zero_mul,zero_div] at hden
    exact hden rfl
  have hxpow : xs j^n≠0 := pow_ne_zero n (div_pos hc hhj).ne'
  have hr : R j≠0 := pow_ne_zero k (mul_pos (by norm_num) (r_pos _ (inverseY_branch _ hxj).1)).ne'
  have hS : S j≠0 := (Finset.prod_pos (fun i _=>boundaryFactor_pos 0 (ts j i))).ne'
  change ((realCoeff (momentTightG P (gs j-k) (2*k) (Ls j)) n*xs j^n /
      (momentTightG P (gs j-k) (2*k) (Ls j) (xs j:ℂ)).re) /
    (realCoeff (Phi P (gs j)) n*xs j^n/markedF P (gs j) 0 (xs j))) *
      ((momentTightG P (gs j-k) (2*k) (Ls j) (xs j:ℂ)).re /
        (markedF P (gs j) 0 (xs j)*R j*S j)) =
      realCoeff (momentTightG P (gs j-k) (2*k) (Ls j)) n /
        (realCoeff (Phi P (gs j)) n*(R j*S j))
  field_simp

lemma connected_coefficient_ratio_bounded (P : PsiTheory) (k n : ℕ)
    (c : ℝ) (hc : 0<c) (B : ℝ) (hB : 0≤B)
    (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop)
    (ts : ℕ→Fin (2*k)→ℝ) (ht : ∀ j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>realCoeff (momentTightG P (gs j-k) (2*k)
      (fun i=>ts j i/tightParameterScale (inverseY (c/(complexity (gs j) 0:ℝ))))) n /
        (realCoeff (Phi P (gs j)) n *
          ((4*r (inverseY (c/(complexity (gs j) 0:ℝ))))^k *
            ∏ i,boundaryFactor 0 (ts j i)))) atTop (𝓝 1) := by
  by_cases hk : k=0
  · subst k
    have hd := connected_phi_poisson_probability_limit P n c hc gs hg
    have hp : 0<Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ) := by positivity
    apply tendsto_const_nhds.congr'
    filter_upwards [hg.eventually_ge_atTop 2,hd.eventually_ne hp.ne'] with j hj hden
    have hCoeff : realCoeff (Phi P (gs j)) n≠0 := by
      intro he
      simp only [he,zero_mul,zero_div] at hden
      exact hden rfl
    have he := connected_momentTightG_zero_coeff P (gs j) hj
      (fun i=>ts j i/tightParameterScale (inverseY (c/(complexity (gs j) 0:ℝ)))) n
    simp only [Nat.sub_zero,Nat.mul_zero,pow_zero,Fintype.prod_empty,mul_one,he,div_self hCoeff]
  · exact connected_coefficient_ratio_bounded_positive_cuts P k n (by omega) c hc B hB gs hg ts ht

end WP.TightConnected
