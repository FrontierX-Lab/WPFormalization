import WPFormalization.Tight.ConnectedPoissonPhi
import WPFormalization.Tight.ConnectedPoissonScale
import WPFormalization.Tight.ConnectedLengthModulus
import WPFormalization.Tight.ConnectedFourierDomination

noncomputable section
namespace WP.TightConnected
open Set Filter TightMoments
open scoped Topology

lemma connected_scaled_factors_tendsto (p : ℕ) (B : ℝ) (qs : ℕ→ℝ)
    (hq : Tendsto qs atTop (𝓝 1)) (hq0 : ∀ᶠ j in atTop,qs j∈Icc (0:ℝ) 2)
    (ts : ℕ→Fin p→ℝ) (ht : ∀ j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>(∏ i,boundaryFactor 0 (qs j*ts j i))/
      (∏ i,boundaryFactor 0 (ts j i))) atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hcont⟩ := connected_scaled_factor_uniform_relative_continuity p B (ε/2) (by positivity)
  have hnear : ∀ᶠ j in atTop,|qs j-1|<δ := by
    simpa only [Real.dist_eq] using hq.eventually (Metric.ball_mem_nhds 1 hδ)
  have he : ∀ᶠ j in atTop,dist ((∏ i,boundaryFactor 0 (qs j*ts j i))/
      (∏ i,boundaryFactor 0 (ts j i))) 1<ε := by
    filter_upwards [hq0,hnear] with j hj hk
    have hb := hcont (qs j) hj (ts j) (ht j) hk
    rw [Real.dist_eq]
    exact hb.trans_lt (by linarith)
  exact eventually_atTop.mp he

lemma connected_tight_profile_tendsto (P : PsiTheory) (p : ℕ) (hp : 1≤p)
    (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop) (xs : ℕ→ℝ)
    (hx : ∀ᶠ j in atTop,xs j∈Ico (0:ℝ) xCritical) (Ls : ℕ→Fin p→ℝ)
    (hL : ∀ᶠ j in atTop,∀ i,0≤Ls j i) (B : ℝ) (hB : 0≤B)
    (hscaled : ∀ᶠ j in atTop,∀ i,tightParameterScale (inverseY (xs j))*Ls j i≤B) :
    Tendsto (fun j=>(momentTightG P (gs j) p (Ls j) (xs j:ℂ)).re /
      (markedF P (gs j) p (xs j)*
        ∏ i,boundaryFactor 0 (tightParameterScale (inverseY (xs j))*Ls j i))) atTop (𝓝 1) := by
  obtain ⟨C,hC,hbound⟩ := tightShiftedPolynomial_uniform_relative_error P p hp B hB
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun j=>norm_nonneg _)) _
    ((tendsto_natCast_atTop_atTop.comp hg).const_div_atTop C)
  filter_upwards [hg.eventually_ge_atTop 2,hx,hL,hscaled] with j hj hxj hLj hsj
  have hs : Stable (gs j) p := by unfold Stable;omega
  have hy := inverseY_branch _ hxj
  have he := hbound (gs j) (by omega) _ hy.1 (Ls j) hLj hsj
  have hshift := string_flow_proof P (gs j) p hs _ hy.1
  rw [hy.2] at hshift
  rw [hshift] at he
  rw [momentTightG_ofReal P (gs j) p (Ls j) _ hxj,Complex.ofReal_re]
  simpa only [Real.norm_eq_abs,Function.comp_def] using he

lemma connected_tight_poisson_normalization (P : PsiTheory) (p : ℕ) (hp : 1≤p)
    (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop)
    (hs : ℕ→ℝ) (hh : Tendsto hs atTop atTop) (c : ℝ) (hc : 0<c)
    (B : ℝ) (hB : 0≤B) (ts : ℕ→Fin p→ℝ) (ht : ∀ j i,ts j i∈Icc (0:ℝ) B)
    (b : ℝ) (hb : 0≤b) :
    Tendsto (fun j=>(momentTightG P (gs j) p
      (fun i=>ts j i/tightParameterScale (inverseY (c/hs j))) ((b/hs j:ℝ):ℂ)).re /
      (markedF P (gs j) p (b/hs j)*∏ i,boundaryFactor 0 (ts j i))) atTop (𝓝 1) := by
  let Ls : ℕ→Fin p→ℝ := fun j i=>ts j i/tightParameterScale (inverseY (c/hs j))
  let qs : ℕ→ℝ := fun j=>tightParameterScale (inverseY (b/hs j))/
    tightParameterScale (inverseY (c/hs j))
  have hq : Tendsto qs atTop (𝓝 1) := connected_origin_parameter_scale_ratio_tendsto hs hh b c hb hc.le
  have hx := connected_small_weight_eventually hs hh c hc.le
  have hy := connected_small_weight_eventually hs hh b hb
  have hq0 : ∀ᶠ j in atTop,qs j∈Icc (0:ℝ) 2 := by
    filter_upwards [hx,hy,hq.eventually (eventually_lt_nhds (by norm_num : (1:ℝ)<2))] with j hj hk hqj
    have hp1:=tightParameterScale_pos _ (inverseY_branch _ hj).1
    have hp2:=tightParameterScale_pos _ (inverseY_branch _ hk).1
    exact ⟨(div_pos hp2 hp1).le,hqj.le⟩
  have hL : ∀ᶠ j in atTop,∀ i,0≤Ls j i := by
    filter_upwards [hx] with j hj i
    exact div_nonneg (ht j i).1 (tightParameterScale_pos _ (inverseY_branch _ hj).1).le
  have hscaled : ∀ᶠ j in atTop,∀ i,tightParameterScale (inverseY (b/hs j))*Ls j i≤2*B := by
    filter_upwards [hq0] with j hj i
    change tightParameterScale (inverseY (b/hs j))*(ts j i/tightParameterScale (inverseY (c/hs j)))≤_
    rw [show tightParameterScale (inverseY (b/hs j))*(ts j i/tightParameterScale (inverseY (c/hs j)))=
      qs j*ts j i by dsimp [qs];ring]
    exact mul_le_mul hj.2 (ht j i).2 (ht j i).1 (by norm_num)
  have hprofile := connected_tight_profile_tendsto P p hp gs hg (fun j=>b/hs j) hy Ls hL (2*B)
    (by positivity) hscaled
  have hfactor := connected_scaled_factors_tendsto p B qs hq hq0 ts ht
  have htend := hprofile.mul hfactor
  simp only [one_mul] at htend
  apply htend.congr'
  filter_upwards [hg.eventually_ge_atTop 2,hx,hy] with j hj hxj hyj
  have hF : markedF P (gs j) p (b/hs j)≠0 :=
    (markedF_positive_cusp_weight P (gs j) p hp (by unfold Stable;omega) _ hyj).ne'
  have hprod : (∏ i,boundaryFactor 0 (qs j*ts j i))≠0 :=
    (Finset.prod_pos (fun i _=>boundaryFactor_pos _ _)).ne'
  change ((momentTightG P (gs j) p (Ls j) ((b/hs j:ℝ):ℂ)).re /
    (markedF P (gs j) p (b/hs j)*∏ i,boundaryFactor 0 (tightParameterScale (inverseY (b/hs j))*Ls j i))) *
    ((∏ i,boundaryFactor 0 (qs j*ts j i))/(∏ i,boundaryFactor 0 (ts j i))) = _
  have hlen (i:Fin p) : tightParameterScale (inverseY (b/hs j))*Ls j i=qs j*ts j i := by
    dsimp [Ls,qs]
    ring
  simp_rw [hlen]
  field_simp
  rfl

lemma connected_tight_poisson_pgf_limit (P : PsiTheory) (p : ℕ) (hp : 1≤p)
    (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop)
    (hs : ℕ→ℝ) (hh : Tendsto hs atTop atTop)
    (hch : Tendsto (fun j=>(complexity (gs j) p:ℝ)/hs j) atTop (𝓝 1))
    (c : ℝ) (hc : 0<c) (B : ℝ) (hB : 0≤B)
    (ts : ℕ→Fin p→ℝ) (ht : ∀ j i,ts j i∈Icc (0:ℝ) B) (z : ℝ) (hz : 0≤z) :
    Tendsto (fun j=>(momentTightG P (gs j) p
      (fun i=>ts j i/tightParameterScale (inverseY (c/hs j))) (((c/hs j)*z:ℝ):ℂ)).re /
      (momentTightG P (gs j) p
        (fun i=>ts j i/tightParameterScale (inverseY (c/hs j))) ((c/hs j:ℝ):ℂ)).re)
      atTop (𝓝 (Real.exp (2*c*(z-1)))) := by
  have ha := connected_tight_poisson_normalization P p hp gs hg hs hh c hc B hB ts ht (c*z) (mul_nonneg hc.le hz)
  have hb := connected_tight_poisson_normalization P p hp gs hg hs hh c hc B hB ts ht c hc.le
  have hm := connected_marked_poisson_pgf_limit P p gs hg hs hh hch c hc z hz
  have htend := (ha.div hb (by norm_num : (1:ℝ)≠0)).mul hm
  simp only [one_div,inv_one,one_mul] at htend
  apply htend.congr'
  filter_upwards [hg.eventually_ge_atTop 2,connected_small_weight_eventually hs hh c hc.le,
    connected_small_weight_eventually hs hh (c*z) (mul_nonneg hc.le hz)] with j hj hx hy
  have hsz : c*z/hs j=(c/hs j)*z := by ring
  rw [hsz] at hy
  have hs' : Stable (gs j) p := by unfold Stable;omega
  have hF : markedF P (gs j) p ((c/hs j)*z)≠0 :=
    (markedF_positive_cusp_weight P _ _ hp hs' _ hy).ne'
  have hFx : markedF P (gs j) p (c/hs j)≠0 :=
    (markedF_positive_cusp_weight P _ _ hp hs' _ hx).ne'
  have hG : (momentTightG P (gs j) p
    (fun i=>ts j i/tightParameterScale (inverseY (c/hs j))) ((c/hs j:ℝ):ℂ)).re≠0 :=
      (momentTightG_real_pos P _ _ hp hs' _ _ hx).ne'
  have hprod : (∏ i,boundaryFactor 0 (ts j i))≠0 :=
    (Finset.prod_pos (fun i _=>boundaryFactor_pos _ _)).ne'
  simp only [Pi.div_apply,hsz]
  field_simp
  rw [hsz]
  exact mul_div_cancel_right₀ _ hF

lemma connected_tight_poisson_probability_limit (P : PsiTheory) (p : ℕ) (hp : 1≤p)
    (gs : ℕ→ℕ) (hg : Tendsto gs atTop atTop)
    (hs : ℕ→ℝ) (hh : Tendsto hs atTop atTop)
    (hch : Tendsto (fun j=>(complexity (gs j) p:ℝ)/hs j) atTop (𝓝 1))
    (c : ℝ) (hc : 0<c) (B : ℝ) (hB : 0≤B)
    (ts : ℕ→Fin p→ℝ) (ht : ∀ j i,ts j i∈Icc (0:ℝ) B) (n : ℕ) :
    Tendsto (fun j=>realCoeff (momentTightG P (gs j) p
      (fun i=>ts j i/tightParameterScale (inverseY (c/hs j)))) n*(c/hs j)^n /
      (momentTightG P (gs j) p
        (fun i=>ts j i/tightParameterScale (inverseY (c/hs j))) ((c/hs j:ℝ):ℂ)).re)
      atTop (𝓝 (Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ))) := by
  let Ls : ℕ→Fin p→ℝ := fun j i=>ts j i/tightParameterScale (inverseY (c/hs j))
  apply positive_pgf_coefficients_tendsto
    (fun j n=>realCoeff (momentTightG P (gs j) p (Ls j)) n*(c/hs j)^n /
      (momentTightG P (gs j) p (Ls j) ((c/hs j:ℝ):ℂ)).re)
    (fun n=>Real.exp (-2*c)*(2*c)^n/(n.factorial:ℝ))
    (fun j z=>(momentTightG P (gs j) p (Ls j) (((c/hs j)*z:ℝ):ℂ)).re /
      (momentTightG P (gs j) p (Ls j) ((c/hs j:ℝ):ℂ)).re)
    (fun z=>Real.exp (2*c*(z-1))) _ (connected_poisson_probability_data c hc.le) _ n
  · filter_upwards [hg.eventually_ge_atTop 2,connected_small_weight_eventually hs hh c hc.le] with j hj hx
    have hstable : Stable (gs j) p := by unfold Stable;omega
    apply connected_probability_data _ (fun x:ℝ=>(momentTightG P (gs j) p (Ls j) (x:ℂ)).re) _ hx.1
      (fun n=>(momentTightG_real_nonnegative_coefficients P _ _ hp hstable (Ls j) n).1)
      (momentTightG_real_pos P _ _ hp hstable (Ls j) _ hx)
    intro z hz
    have hxz : (c/hs j)*z∈Ico (0:ℝ) xCritical :=
      ⟨mul_nonneg hx.1 hz.1,(mul_le_of_le_one_right hx.1 hz.2).trans_lt hx.2⟩
    exact connected_real_taylor_hasSum _ _ (momentTightG_taylor P _ _ _ _
      (by rw [Complex.norm_of_nonneg hxz.1];exact hxz.2))
  · intro z hz
    exact connected_tight_poisson_pgf_limit P p hp gs hg hs hh hch c hc B hB ts ht z hz.1.le

end WP.TightConnected
