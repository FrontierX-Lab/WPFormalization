import WPFormalization.Analysis.GevreyOnePointwise
import WPFormalization.Analysis.GevreyOneShift
import WPFormalization.Analysis.GevreyOneInverse
import WPFormalization.Analysis.GevreyOneLog
/-! Actual Gevrey-one expansions along unbounded discrete scales. No real
interpolation of the numerical sequence is used. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open Filter PowerSeries
open scoped Topology

def GevreyOneSequence (scale F:ℕ→ℝ)(f:WP.HigherOrder.Series):Prop:=
  ∃(C B c:ℝ)(N₀:ℕ),0<C ∧ 0<B ∧ 0<c ∧ ∀n:ℕ,N₀≤n→
    0< scale n ∧ ∀K:ℕ,(K:ℝ)≤c*scale n→
      |F n-inversePowerTruncation f K (scale n)|≤
        C*B^(K+1)*((K+1).factorial:ℝ)/(scale n)^(K+1)

lemma GevreyOneSequence.of_real (scale:ℕ→ℝ)(hs:Tendsto scale atTop atTop)
    (F:ℝ→ℝ)(f:WP.HigherOrder.Series)(hF:GevreyOneAsymptotic F f):
    GevreyOneSequence scale (fun n=>F (scale n)) f:=by
  obtain ⟨C,B,c,h₀,hC,hB,hc,hh₀,herr⟩:=hF
  obtain ⟨N,hN⟩:=eventually_atTop.1 (hs.eventually (eventually_ge_atTop h₀))
  refine ⟨C,B,c,N,hC,hB,hc,?_⟩
  intro n hn
  have hh:h₀≤ scale n:=hN n hn
  exact ⟨lt_of_lt_of_le hh₀ hh,fun K hK=>herr K (scale n) hh hK⟩

lemma GevreyOneSequence.coeff_bound (scale F:ℕ→ℝ) (hs:Tendsto scale atTop atTop)
    (f:WP.HigherOrder.Series) (hF:GevreyOneSequence scale F f) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀n:ℕ,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ) := by
  obtain ⟨C,B,c,N₀,hC,hB,hc,hall⟩:=hF
  refine ⟨C+|PowerSeries.constantCoeff f|,B,by positivity,hB,?_⟩
  intro n
  cases n with
  | zero=>simp only [PowerSeries.coeff_zero_eq_constantCoeff,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one];linarith
  | succ n=>
    have hcoeff:|PowerSeries.coeff (n+1) f|≤C*B^(n+1)*((n+1).factorial:ℝ) := by
      let A:ℝ:=C*B^(n+1)*((n+1).factorial:ℝ)
      let D:ℝ:=C*B^(n+2)*((n+2).factorial:ℝ)
      have hlim:Tendsto (fun m:ℕ=>A+D/scale m) atTop (𝓝 A) := by
        have hd:Tendsto (fun m:ℕ=>D*(scale m)⁻¹) atTop (𝓝 0) := by
          simpa only [Function.comp_apply,mul_zero] using (tendsto_const_nhds : Tendsto (fun _:ℕ=>D) atTop (𝓝 D)).mul (tendsto_inv_atTop_zero.comp hs)
        simpa only [div_eq_mul_inv,add_zero] using (tendsto_const_nhds : Tendsto (fun _:ℕ=>A) atTop (𝓝 A)).add hd
      change |PowerSeries.coeff (n+1) f|≤A
      apply ge_of_tendsto hlim
      filter_upwards [eventually_ge_atTop N₀,hs.eventually (eventually_ge_atTop (((n+1:ℕ):ℝ)/c))] with m hm hwindow
      let h:ℝ:=scale m
      have hdata:=hall m hm
      have hp:0<h:=hdata.1
      have hw:(n+1:ℕ)≤c*h := by
        have he:((n+1:ℕ):ℝ)≤h*c := (div_le_iff₀ hc).mp hwindow
        simpa only [mul_comm] using he
      have hw₀:(n:ℝ)≤c*h := by exact le_trans (by norm_num) hw
      have he₀:=hdata.2 n hw₀
      have he₁:=hdata.2 (n+1) hw
      have hdiff:inversePowerTruncation f (n+1) h-inversePowerTruncation f n h=
          PowerSeries.coeff (n+1) f/h^(n+1) := by
        dsimp only [inversePowerTruncation]
        rw [Finset.sum_range_succ]
        ring
      have he:|PowerSeries.coeff (n+1) f/h^(n+1)|≤
          C*B^(n+2)*((n+2).factorial:ℝ)/h^(n+2)+C*B^(n+1)*((n+1).factorial:ℝ)/h^(n+1) := by
        rw [←hdiff]
        calc
          _ ≤ |inversePowerTruncation f (n+1) h-F m|+|F m-inversePowerTruncation f n h| := abs_sub_le _ _ _
          _ ≤ _ := add_le_add (by simpa only [abs_sub_comm,Nat.add_assoc] using he₁) he₀
      have hpow:0<h^(n+1):=pow_pos hp _
      rw [abs_div,abs_of_pos hpow] at he
      have he':|PowerSeries.coeff (n+1) f|≤
          (C*B^(n+2)*((n+2).factorial:ℝ)/h^(n+2)+C*B^(n+1)*((n+1).factorial:ℝ)/h^(n+1))*h^(n+1) :=
        (div_le_iff₀ hpow).mp he
      convert he' using 1
      dsimp[A,D,h]
      rw [show n+2=(n+1)+1 by omega,pow_succ]
      field_simp [show scale m≠0 from hp.ne']
      ring
    exact hcoeff.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith[abs_nonneg (PowerSeries.constantCoeff f)] : C≤C+|PowerSeries.constantCoeff f|)
      (pow_nonneg hB.le _)) (Nat.cast_nonneg _))



lemma GevreyOneSequence.mul (scale F G:ℕ→ℝ)(hs:Tendsto scale atTop atTop)
    (f g:WP.HigherOrder.Series)(hF:GevreyOneSequence scale F f)(hG:GevreyOneSequence scale G g):
    GevreyOneSequence scale (fun n=>F n*G n) (f*g):=by
  obtain ⟨Cf,Bf,hCf,hBf,hfc⟩:=GevreyOneSequence.coeff_bound scale F hs f hF
  obtain ⟨Cg,Bg,hCg,hBg,hgc⟩:=GevreyOneSequence.coeff_bound scale G hs g hG
  obtain ⟨CF,BF,cF,NF,hCF,hBF,hcF,hFerr⟩:=hF
  obtain ⟨CG,BG,cG,NG,hCG,hBG,hcG,hGerr⟩:=hG
  let C₀:ℝ:=Cf+Cg
  let B₀:ℝ:=Bf+Bg
  have hC₀:0<C₀:=by dsimp[C₀];positivity
  have hB₀:0<B₀:=by dsimp[B₀];positivity
  have hf:∀n,|PowerSeries.coeff n f|≤C₀*B₀^n*(n.factorial:ℝ):=by
    intro n
    apply (hfc n).trans
    dsimp[C₀,B₀]
    gcongr <;> linarith
  have hg:∀n,|PowerSeries.coeff n g|≤C₀*B₀^n*(n.factorial:ℝ):=by
    intro n
    apply (hgc n).trans
    dsimp[C₀,B₀]
    gcongr <;> linarith
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 (hs.eventually (eventually_ge_atTop (max 1 (8*B₀))))
  let c:ℝ:=min cF (min cG (1/(8*B₀)))
  let N:ℕ:=max (max NF NG) N₁
  let MG:ℝ:=|PowerSeries.coeff 0 g|+CG*BG
  have hMG:0<MG:=by dsimp[MG];positivity
  let B:ℝ:=BF+BG+2*B₀*Real.exp 1
  let C:ℝ:=CF*MG+2*C₀*CG+8*C₀^2
  refine ⟨C,B,c,N,by dsimp[C];positivity,by dsimp[B];positivity,
    lt_min hcF (lt_min hcG (by positivity)),?_⟩
  intro n hn
  have hnF:NF≤n:=((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hnG:NG≤n:=((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  let h:ℝ:=scale n
  have h₁:max 1 (8*B₀)≤h:=hN₁ n hn₁
  have hh1:1≤h:=(le_max_left _ _).trans h₁
  have hhB:8*B₀≤h:=(le_max_right _ _).trans h₁
  have hh:0<h:=lt_of_lt_of_le zero_lt_one hh1
  have hFd:=hFerr n hnF
  have hGd:=hGerr n hnG
  refine ⟨hh,?_⟩
  intro K hK
  have hKF:(K:ℝ)≤cF*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hh.le)
  have hKG:(K:ℝ)≤cG*h:=hK.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) hh.le)
  have hKr:(K:ℝ)≤(1/(8*B₀))*h:=hK.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) hh.le)
  have hwindow:4*B₀*((K:ℝ)+1)≤h:=by
    have hk':(K:ℝ)*(8*B₀)≤h:=(le_div_iff₀ (by positivity:0<8*B₀)).mp
      (by simpa only[one_div,mul_comm,div_eq_mul_inv,one_mul] using hKr)
    nlinarith
  have hGval:|G n|≤MG:=by
    have he:=hGd.2 0 (by have hp:=mul_pos hcG hh;simpa only[Nat.cast_zero] using hp.le)
    simp only[inversePowerTruncation,Finset.sum_range_one,pow_zero,div_one,Nat.zero_add,pow_one,
      Nat.factorial_one,Nat.cast_one,mul_one] at he
    calc
      _ = |(G n-PowerSeries.coeff 0 g)+PowerSeries.coeff 0 g|:=by congr 1;ring
      _ ≤ |G n-PowerSeries.coeff 0 g|+|PowerSeries.coeff 0 g|:=abs_add_le _ _
      _ ≤ CG*BG/h+|PowerSeries.coeff 0 g|:=add_le_add he le_rfl
      _ ≤ MG:=by dsimp[MG];have hd:=div_le_self (mul_nonneg hCG.le hBG.le) hh1;linarith
  have he:=mul_value_truncation_error f g C₀ B₀ hC₀.le hB₀ hf hg K h hh hwindow
    (F n) (G n) (CF*BF^(K+1)*((K+1).factorial:ℝ)/h^(K+1))
    (CG*BG^(K+1)*((K+1).factorial:ℝ)/h^(K+1)) MG (hFd.2 K hKF) (hGd.2 K hKG) hGval
  have hbF:BF≤B:=by
    dsimp[B]
    have hp:0<2*B₀*Real.exp 1:=by positivity
    linarith
  have hbG:BG≤B:=by
    dsimp[B]
    have hp:0<2*B₀*Real.exp 1:=by positivity
    linarith
  have hbP:2*B₀*Real.exp 1≤B:=by dsimp[B];linarith
  calc
    _ ≤ MG*(CF*BF^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        2*C₀*(CG*BG^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        8*C₀^2*(2*B₀*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=he
    _ ≤ MG*(CF*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        2*C₀*(CG*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        8*C₀^2*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring


lemma GevreyOneSequence.inv_unit (scale F:ℕ→ℝ)(hs:Tendsto scale atTop atTop)
    (f:WP.HigherOrder.Series)(hF:GevreyOneSequence scale F f)(hf0:PowerSeries.constantCoeff f=1):
    GevreyOneSequence scale (fun n=>(F n)⁻¹) (f⁻¹):=by
  obtain ⟨C₀,B₀,hC₀,hB₀,hcoeff⟩:=GevreyOneSequence.coeff_bound scale F hs f hF
  obtain ⟨C₁,B₁,q,N₀,hC₁,hB₁,hq,herr⟩:=hF
  let T:ℝ:=(C₀+1)*B₀
  have hT:0<T:=by dsimp[T];positivity
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 (hs.eventually
    (eventually_ge_atTop (max (32*T) (2*C₁*B₁+1))))
  let q':ℝ:=min q (1/(32*T))
  let N:ℕ:=max N₀ N₁
  let B:ℝ:=B₁+8*T*Real.exp 1
  let C:ℝ:=4*C₁+4
  refine ⟨C,B,q',N,by dsimp[C];positivity,by dsimp[B];positivity,lt_min hq (by positivity),?_⟩
  intro n hn
  have hn₀:N₀≤n:=(le_max_left _ _).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  have hd:=herr n hn₀
  let h:ℝ:=scale n
  have hh:0<h:=hd.1
  have hl:max (32*T) (2*C₁*B₁+1)≤h:=hN₁ n hn₁
  have hhT:32*T≤h:=(le_max_left _ _).trans hl
  have hhC:2*C₁*B₁+1≤h:=(le_max_right _ _).trans hl
  refine ⟨hh,?_⟩
  intro K hK
  have hKq:(K:ℝ)≤q*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hh.le)
  have hKr:(K:ℝ)≤(1/(32*T))*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hh.le)
  have hwindow:16*T*((K:ℝ)+1)≤h:=by
    have hk':(K:ℝ)*(32*T)≤h:=(le_div_iff₀ (by positivity:0<32*T)).mp
      (by simpa only[one_div,mul_comm,div_eq_mul_inv,one_mul] using hKr)
    nlinarith
  have hx0:|F n-1|≤1/2:=by
    have he:=hd.2 0 (by have hpos:=mul_pos hq hh;simpa only[Nat.cast_zero] using hpos.le)
    simp only[inversePowerTruncation,Finset.sum_range_one,pow_zero,div_one,Nat.zero_add,pow_one,
      Nat.factorial_one,Nat.cast_one,mul_one,PowerSeries.coeff_zero_eq_constantCoeff,hf0] at he
    apply he.trans
    apply (div_le_iff₀ hh).mpr
    linarith
  have he:=inverse_value_truncation_error f C₀ B₀ hC₀.le hB₀ hf0 hcoeff K h hh
    (by simpa only[T,mul_assoc] using hwindow)
    (F n) (C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1)) hx0 (hd.2 K hKq)
  have hb₁:B₁≤B:=le_add_of_nonneg_right (by positivity)
  have hb₂:8*T*Real.exp 1≤B:=le_add_of_nonneg_left hB₁.le
  calc
    _ ≤ 4*(C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        4*(8*T*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by simpa only[T,mul_assoc] using he
    _ ≤ 4*(C₁*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        4*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring

lemma GevreyOneSequence.log_unit (scale F:ℕ→ℝ)(hs:Tendsto scale atTop atTop)
    (f:WP.HigherOrder.Series)(hF:GevreyOneSequence scale F f)(hf0:PowerSeries.constantCoeff f=1):
    GevreyOneSequence scale (fun n=>Real.log (F n)) (WP.HigherOrder.finiteLog f):=by
  obtain ⟨C₀,B₀,hC₀,hB₀,hcoeff⟩:=GevreyOneSequence.coeff_bound scale F hs f hF
  obtain ⟨C₁,B₁,q,N₀,hC₁,hB₁,hq,herr⟩:=hF
  let T:ℝ:=(C₀+1)*B₀
  have hT:0<T:=by dsimp[T];positivity
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 (hs.eventually
    (eventually_ge_atTop (max (32*T) (2*C₁*B₁+1))))
  let q':ℝ:=min q (1/(32*T))
  let N:ℕ:=max N₀ N₁
  let B:ℝ:=B₁+8*T*Real.exp 1
  let C:ℝ:=2*C₁+2
  refine ⟨C,B,q',N,by dsimp[C];positivity,by dsimp[B];positivity,lt_min hq (by positivity),?_⟩
  intro n hn
  have hn₀:N₀≤n:=(le_max_left _ _).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  have hd:=herr n hn₀
  let h:ℝ:=scale n
  have hh:0<h:=hd.1
  have hl:max (32*T) (2*C₁*B₁+1)≤h:=hN₁ n hn₁
  have hhT:32*T≤h:=(le_max_left _ _).trans hl
  have hhC:2*C₁*B₁+1≤h:=(le_max_right _ _).trans hl
  refine ⟨hh,?_⟩
  intro K hK
  have hKq:(K:ℝ)≤q*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hh.le)
  have hKr:(K:ℝ)≤(1/(32*T))*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hh.le)
  have hwindow:16*T*((K:ℝ)+1)≤h:=by
    have hk':(K:ℝ)*(32*T)≤h:=(le_div_iff₀ (by positivity:0<32*T)).mp
      (by simpa only[one_div,mul_comm,div_eq_mul_inv,one_mul] using hKr)
    nlinarith
  have hx0:|F n-1|≤1/2:=by
    have he:=hd.2 0 (by have hpos:=mul_pos hq hh;simpa only[Nat.cast_zero] using hpos.le)
    simp only[inversePowerTruncation,Finset.sum_range_one,pow_zero,div_one,Nat.zero_add,pow_one,
      Nat.factorial_one,Nat.cast_one,mul_one,PowerSeries.coeff_zero_eq_constantCoeff,hf0] at he
    apply he.trans
    apply (div_le_iff₀ hh).mpr
    linarith
  have he:=log_value_truncation_error f C₀ B₀ hC₀.le hB₀ hf0 hcoeff K h hh
    (by simpa only[T,mul_assoc] using hwindow)
    (F n) (C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1)) hx0 (hd.2 K hKq)
  have hb₁:B₁≤B:=le_add_of_nonneg_right (by positivity)
  have hb₂:8*T*Real.exp 1≤B:=le_add_of_nonneg_left hB₁.le
  calc
    _ ≤ 2*(C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        2*(8*T*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by simpa only[T,mul_assoc] using he
    _ ≤ 2*(C₁*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        2*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring


lemma scale_add_const_tendsto (scale:ℕ→ℝ)(hs:Tendsto scale atTop atTop)(c:ℝ):
    Tendsto (fun n=>scale n+c) atTop atTop:=by
  apply tendsto_atTop.2
  intro b
  filter_upwards [hs.eventually (eventually_ge_atTop (b-c))] with n hn
  linarith

lemma GevreyOneSequence.shift (scale F:ℕ→ℝ)(hs:Tendsto scale atTop atTop)
    (f:WP.HigherOrder.Series)(hF:GevreyOneSequence scale F f)(c:ℝ):
    GevreyOneSequence (fun n=>scale n+c) F (WP.HigherOrder.complexityShift c f):=by
  obtain ⟨C₀,B₀,hC₀,hB₀,hcoeff⟩:=GevreyOneSequence.coeff_bound scale F hs f hF
  obtain ⟨C₁,B₁,q,N₀,hC₁,hB₁,hq,herr⟩:=hF
  let T:ℝ:=B₀+|c|+1
  have hT:0<T:=by dsimp[T];positivity
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 (hs.eventually
    (eventually_ge_atTop (max (|c|+1) (16*T+|c|))))
  let q':ℝ:=min (q/2) (1/(16*T))
  let N:ℕ:=max N₀ N₁
  let B:ℝ:=2*B₁+4*T*Real.exp 1
  let C:ℝ:=C₁+4*C₀
  refine ⟨C,B,q',N,by dsimp[C];positivity,by dsimp[B];positivity,
    lt_min (by positivity) (by positivity),?_⟩
  intro n hn
  have hn₀:N₀≤n:=(le_max_left _ _).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  have hd:=herr n hn₀
  have hl:max (|c|+1) (16*T+|c|)≤ scale n:=hN₁ n hn₁
  have hs₁:|c|+1≤ scale n:=(le_max_left _ _).trans hl
  have hsT:16*T+|c|≤ scale n:=(le_max_right _ _).trans hl
  let h:ℝ:=scale n+c
  have hh:0<h:=by dsimp[h];have hc:=neg_abs_le c;linarith
  have hhT:16*T≤h:=by dsimp[h];have hc:=neg_abs_le c;linarith
  have hhalf:0<h/2:=by positivity
  have hhalfU:h/2≤ scale n:=by dsimp[h];have hc:=le_abs_self c;linarith
  have hu:h-c=scale n:=by dsimp[h];ring
  refine ⟨hh,?_⟩
  intro K hK
  have hKq:(K:ℝ)≤q*scale n:=by
    have hk:(K:ℝ)≤(q/2)*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hh.le)
    have he:=mul_le_mul_of_nonneg_left hhalfU hq.le
    nlinarith
  have hKr:(K:ℝ)≤(1/(16*T))*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hh.le)
  have hwindow:8*T*((K:ℝ)+1)≤h:=by
    have hk':(K:ℝ)*(16*T)≤h:=(le_div_iff₀ (by positivity:0<16*T)).mp
      (by simpa only[one_div,mul_comm,div_eq_mul_inv,one_mul] using hKr)
    nlinarith
  have he:=hd.2 K hKq
  have hactual:|F n-inversePowerTruncation f K (scale n)|≤
      C₁*(2*B₁)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
    apply he.trans
    calc
      _ ≤ C₁*B₁^(K+1)*((K+1).factorial:ℝ)/(h/2)^(K+1):=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hhalf _)
          (pow_le_pow_left₀ hhalf.le hhalfU _)
      _ = _:=by rw[div_pow,mul_pow];field_simp
  have htail:=shifted_truncated_polynomial_real_remainder f c C₀ B₀ hC₀.le hB₀ hcoeff K h hh
    (by rw[hu];exact hd.1) hwindow
  rw[hu] at htail
  have hb₁:2*B₁≤B:=le_add_of_nonneg_right (by positivity)
  have hb₂:4*T*Real.exp 1≤B:=le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ |F n-inversePowerTruncation f K (scale n)|+
        |inversePowerTruncation f K (scale n)-inversePowerTruncation (WP.HigherOrder.complexityShift c f) K h|:=abs_sub_le _ _ _
    _ ≤ C₁*(2*B₁)^(K+1)*((K+1).factorial:ℝ)/h^(K+1)+
        4*C₀*(4*T*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=add_le_add hactual htail
    _ ≤ C₁*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1)+
        4*C₀*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring


lemma GevreyOneSequence.congr (scale F G:ℕ→ℝ)(f:WP.HigherOrder.Series)
    (hF:GevreyOneSequence scale F f)(he:F=ᶠ[atTop] G):GevreyOneSequence scale G f:=by
  obtain ⟨C,B,c,N₀,hC,hB,hc,herr⟩:=hF
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 he
  refine ⟨C,B,c,max N₀ N₁,hC,hB,hc,?_⟩
  intro n hn
  have hn₀:N₀≤n:=(le_max_left _ _).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  have hd:=herr n hn₀
  rw[←hN₁ n hn₁]
  exact hd

lemma GevreyOneSequence.congr_scale (s t F:ℕ→ℝ)(f:WP.HigherOrder.Series)
    (hF:GevreyOneSequence s F f)(he:s=ᶠ[atTop] t):GevreyOneSequence t F f:=by
  obtain ⟨C,B,c,N₀,hC,hB,hc,herr⟩:=hF
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 he
  refine ⟨C,B,c,max N₀ N₁,hC,hB,hc,?_⟩
  intro n hn
  have hn₀:N₀≤n:=(le_max_left _ _).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  rw[←hN₁ n hn₁]
  exact herr n hn₀

end WP.Analysis
