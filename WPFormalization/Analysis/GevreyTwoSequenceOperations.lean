import WPFormalization.Analysis.GevreyTwoPointwise
noncomputable section
namespace WP.Analysis
open Filter PowerSeries
open scoped Topology
lemma GevreyTwoSequence.mul (scale F G:ℕ→ℝ)(hs:Tendsto scale atTop atTop)
    (f g:WP.HigherOrder.Series)(hF:GevreyTwoSequence scale F f)(hG:GevreyTwoSequence scale G g):
    GevreyTwoSequence scale (fun n=>F n*G n) (f*g):=by
  obtain ⟨Cf,Bf,hCf,hBf,hfc⟩:=GevreyTwoSequence.coeff_bound scale F hs f hF
  obtain ⟨Cg,Bg,hCg,hBg,hgc⟩:=GevreyTwoSequence.coeff_bound scale G hs g hG
  obtain ⟨CF,BF,cF,NF,hCF,hBF,hcF,hFerr⟩:=hF
  obtain ⟨CG,BG,cG,NG,hCG,hBG,hcG,hGerr⟩:=hG
  let C₀:ℝ:=Cf+Cg
  let B₀:ℝ:=Bf+Bg
  have hC₀:0<C₀:=by dsimp[C₀];positivity
  have hB₀:0<B₀:=by dsimp[B₀];positivity
  have hf:∀n,|PowerSeries.coeff n f|≤C₀*B₀^n*(n.factorial:ℝ)^2:=by
    intro n
    apply (hfc n).trans
    dsimp[C₀,B₀]
    gcongr <;> linarith
  have hg:∀n,|PowerSeries.coeff n g|≤C₀*B₀^n*(n.factorial:ℝ)^2:=by
    intro n
    apply (hgc n).trans
    dsimp[C₀,B₀]
    gcongr <;> linarith
  obtain ⟨c,H,hc,hcc,hH,hwindowAll⟩:=gevreyTwo_cauchy_window B₀ (min cF cG) hB₀ (lt_min hcF hcG)
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 (hs.eventually (eventually_ge_atTop (max 1 H)))
  let N:ℕ:=max (max NF NG) N₁
  let MG:ℝ:=|PowerSeries.coeff 0 g|+CG*BG
  have hMG:0<MG:=by dsimp[MG];positivity
  let B:ℝ:=BF+BG+2*B₀*(Real.exp 1)^2
  let C:ℝ:=CF*MG+2*C₀*CG+8*C₀^2
  refine ⟨C,B,c,N,by dsimp[C];positivity,by dsimp[B];positivity,
    hc,?_⟩
  intro n hn
  have hnF:NF≤n:=((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hnG:NG≤n:=((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  let h:ℝ:=scale n
  have h₁:max 1 H≤h:=hN₁ n hn₁
  have hh1:1≤h:=(le_max_left _ _).trans h₁
  have hhH:H≤h:=(le_max_right _ _).trans h₁
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hFd:=hFerr n hnF
  have hGd:=hGerr n hnG
  refine ⟨hh,?_⟩
  intro K hK
  have hKF:(K:ℝ)≤cF*Real.sqrt h:=hK.trans (mul_le_mul_of_nonneg_right
    (hcc.trans (min_le_left _ _)) (Real.sqrt_nonneg _))
  have hKG:(K:ℝ)≤cG*Real.sqrt h:=hK.trans (mul_le_mul_of_nonneg_right
    (hcc.trans (min_le_right _ _)) (Real.sqrt_nonneg _))
  have hwindow:4*B₀*((K:ℝ)+1)^2≤h:=hwindowAll h hhH K hK
  have hGval:|G n|≤MG:=by
    have he:=hGd.2 0 (by have hp:=mul_pos hcG (Real.sqrt_pos.mpr hh);simpa only[Nat.cast_zero] using hp.le)
    simp only[inversePowerTruncation,Finset.sum_range_one,pow_zero,div_one,Nat.zero_add,pow_one,
      Nat.factorial_one,Nat.cast_one,one_pow,mul_one] at he
    calc
      _ = |(G n-PowerSeries.coeff 0 g)+PowerSeries.coeff 0 g|:=by congr 1;ring
      _ ≤ |G n-PowerSeries.coeff 0 g|+|PowerSeries.coeff 0 g|:=abs_add_le _ _
      _ ≤ CG*BG/h+|PowerSeries.coeff 0 g|:=add_le_add he le_rfl
      _ ≤ MG:=by dsimp[MG];have hd:=div_le_self (mul_nonneg hCG.le hBG.le) hh1;linarith
  have he:=mul_value_gevreyTwo_truncation_error f g C₀ B₀ hC₀.le hB₀ hf hg K h hh hwindow
    (F n) (G n) (CF*BF^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))
    (CG*BG^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)) MG (hFd.2 K hKF) (hGd.2 K hKG) hGval
  have hbF:BF≤B:=by
    dsimp[B]
    have hp:0<2*B₀*(Real.exp 1)^2:=by positivity
    linarith
  have hbG:BG≤B:=by
    dsimp[B]
    have hp:0<2*B₀*(Real.exp 1)^2:=by positivity
    linarith
  have hbP:2*B₀*(Real.exp 1)^2≤B:=by dsimp[B];linarith
  calc
    _ ≤ MG*(CF*BF^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))+
        2*C₀*(CG*BG^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))+
        8*C₀^2*(2*B₀*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=he
    _ ≤ MG*(CF*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))+
        2*C₀*(CG*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))+
        8*C₀^2*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring



lemma GevreyTwoSequence.of_gevreyOne (scale F:ℕ→ℝ)(hs:Tendsto scale atTop atTop)
    (f:HigherOrder.Series)(hF:GevreyOneSequence scale F f):GevreyTwoSequence scale F f:=by
  obtain ⟨C,B,c,N,hC,hB,hc,herr⟩:=hF
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 (hs.eventually (eventually_ge_atTop 1))
  refine ⟨C,B,c,max N N₁,hC,hB,hc,?_⟩
  intro n hn
  have hd:=herr n ((le_max_left _ _).trans hn)
  have hh1:1≤ scale n:=hN₁ n ((le_max_right _ _).trans hn)
  refine ⟨hd.1,?_⟩
  intro K hK
  have hsq:Real.sqrt (scale n)≤ scale n:=by
    have hs0:=Real.sqrt_nonneg (scale n)
    have hs2:=Real.sq_sqrt hd.1.le
    nlinarith
  apply (hd.2 K (hK.trans (mul_le_mul_of_nonneg_left hsq hc.le))).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hf1:(1:ℝ)≤(K+1).factorial:=by exact_mod_cast Nat.factorial_pos (K+1)
  nlinarith

lemma GevreyTwoSequence.congr (scale F G:ℕ→ℝ)(f:WP.HigherOrder.Series)
    (hF:GevreyTwoSequence scale F f)(he:F=ᶠ[atTop] G):GevreyTwoSequence scale G f:=by
  obtain ⟨C,B,c,N₀,hC,hB,hc,herr⟩:=hF
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 he
  refine ⟨C,B,c,max N₀ N₁,hC,hB,hc,?_⟩
  intro n hn
  have hn₀:N₀≤n:=(le_max_left _ _).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  have hd:=herr n hn₀
  rw[←hN₁ n hn₁]
  exact hd

lemma GevreyTwoSequence.congr_scale (s t F:ℕ→ℝ)(f:WP.HigherOrder.Series)
    (hF:GevreyTwoSequence s F f)(he:s=ᶠ[atTop] t):GevreyTwoSequence t F f:=by
  obtain ⟨C,B,c,N₀,hC,hB,hc,herr⟩:=hF
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 he
  refine ⟨C,B,c,max N₀ N₁,hC,hB,hc,?_⟩
  intro n hn
  have hn₀:N₀≤n:=(le_max_left _ _).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  rw[←hN₁ n hn₁]
  exact herr n hn₀


end WP.Analysis
