import WPFormalization.Analysis.GevreyOneSequence
import WPFormalization.Analysis.FiniteExpGevreyTwo
import WPFormalization.Analysis.GevreyTwoWindow
/-! Gevrey-two expansions on genuine discrete scales. The coefficient bound
is deduced from the actual all-order errors; no interpolation is assumed. -/
noncomputable section
namespace WP.Analysis
open Filter PowerSeries
open scoped Topology

def GevreyTwoSequence (scale F:ℕ→ℝ)(f:WP.HigherOrder.Series):Prop:=
  ∃(C B c:ℝ)(N₀:ℕ),0<C ∧ 0<B ∧ 0<c ∧ ∀n:ℕ,N₀≤n→
    0<scale n ∧ ∀K:ℕ,(K:ℝ)≤c*Real.sqrt (scale n)→
      |F n-inversePowerTruncation f K (scale n)|≤
        C*B^(K+1)*((K+1).factorial:ℝ)^2/(scale n)^(K+1)

lemma GevreyTwoSequence.coeff_bound (scale F:ℕ→ℝ) (hs:Tendsto scale atTop atTop)
    (f:WP.HigherOrder.Series) (hF:GevreyTwoSequence scale F f) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀n:ℕ,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ)^2 := by
  obtain ⟨C,B,c,N₀,hC,hB,hc,hall⟩:=hF
  refine ⟨C+|PowerSeries.constantCoeff f|,B,by positivity,hB,?_⟩
  intro n
  cases n with
  | zero=>simp only [PowerSeries.coeff_zero_eq_constantCoeff,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one];linarith
  | succ n=>
    have hcoeff:|PowerSeries.coeff (n+1) f|≤C*B^(n+1)*((n+1).factorial:ℝ)^2 := by
      let A:ℝ:=C*B^(n+1)*((n+1).factorial:ℝ)^2
      let D:ℝ:=C*B^(n+2)*((n+2).factorial:ℝ)^2
      have hlim:Tendsto (fun m:ℕ=>A+D/scale m) atTop (𝓝 A) := by
        have hd:Tendsto (fun m:ℕ=>D*(scale m)⁻¹) atTop (𝓝 0) := by
          simpa only [Function.comp_apply,mul_zero] using (tendsto_const_nhds : Tendsto (fun _:ℕ=>D) atTop (𝓝 D)).mul (tendsto_inv_atTop_zero.comp hs)
        simpa only [div_eq_mul_inv,add_zero] using (tendsto_const_nhds : Tendsto (fun _:ℕ=>A) atTop (𝓝 A)).add hd
      change |PowerSeries.coeff (n+1) f|≤A
      apply ge_of_tendsto hlim
      filter_upwards [eventually_ge_atTop N₀,hs.eventually (eventually_ge_atTop ((((n+1:ℕ):ℝ)/c)^2))] with m hm hwindow
      let h:ℝ:=scale m
      have hdata:=hall m hm
      have hp:0<h:=hdata.1
      have hw:((n+1:ℕ):ℝ)≤c*Real.sqrt h:=by
        have he:=mul_le_mul_of_nonneg_left hwindow (sq_nonneg c)
        have heq:c^2*((((n+1:ℕ):ℝ)/c)^2)=((n+1:ℕ):ℝ)^2:=by field_simp
        change c^2*((((n+1:ℕ):ℝ)/c)^2)≤c^2*h at he
        rw[heq] at he
        have hs0:=Real.sqrt_nonneg h
        have hs2:=Real.sq_sqrt hp.le
        have hc0:=mul_nonneg hc.le hs0
        nlinarith
      have hw₀:(n:ℝ)≤c*Real.sqrt h:=by exact le_trans (by norm_num) hw
      have he₀:=hdata.2 n hw₀
      have he₁:=hdata.2 (n+1) hw
      have hdiff:inversePowerTruncation f (n+1) h-inversePowerTruncation f n h=
          PowerSeries.coeff (n+1) f/h^(n+1) := by
        dsimp only [inversePowerTruncation]
        rw [Finset.sum_range_succ]
        ring
      have he:|PowerSeries.coeff (n+1) f/h^(n+1)|≤
          C*B^(n+2)*((n+2).factorial:ℝ)^2/h^(n+2)+C*B^(n+1)*((n+1).factorial:ℝ)^2/h^(n+1) := by
        rw [←hdiff]
        calc
          _ ≤ |inversePowerTruncation f (n+1) h-F m|+|F m-inversePowerTruncation f n h| := abs_sub_le _ _ _
          _ ≤ _ := add_le_add (by simpa only [abs_sub_comm,Nat.add_assoc] using he₁) he₀
      have hpow:0<h^(n+1):=pow_pos hp _
      rw [abs_div,abs_of_pos hpow] at he
      have he':|PowerSeries.coeff (n+1) f|≤
          (C*B^(n+2)*((n+2).factorial:ℝ)^2/h^(n+2)+C*B^(n+1)*((n+1).factorial:ℝ)^2/h^(n+1))*h^(n+1) :=
        (div_le_iff₀ hpow).mp he
      convert he' using 1
      dsimp[A,D,h]
      rw [show n+2=(n+1)+1 by omega,pow_succ]
      field_simp [show scale m≠0 from hp.ne']
      ring
    exact hcoeff.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith[abs_nonneg (PowerSeries.constantCoeff f)] : C≤C+|PowerSeries.constantCoeff f|)
      (pow_nonneg hB.le _)) (by positivity))




end WP.Analysis
