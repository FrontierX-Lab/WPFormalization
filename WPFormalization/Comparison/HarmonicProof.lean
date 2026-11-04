import WPFormalization.Statements.LowerComparison
import WPFormalization.Statements.UpperComparison
noncomputable section
namespace WP
open Set
lemma clippedWeight_fixed_length (c:ℝ)(hc:0 ≤ c)(n:ℕ)(d:List ℕ)(hn:d.length=n):
    clippedWeight c d ≤ (4:ℝ)^n*(max 1 (c*Real.sqrt (n+1)))^n := by
  have hz:zeros d ≤ n:=by simpa only [zeros,←hn] using List.length_filter_le (fun k=>k=0) d
  have hi:inactive d ≤ n:=by simpa only [inactive,←hn] using List.length_filter_le (fun k=>k ≤ 1) d
  have hM:1 ≤ max 1 (c*Real.sqrt (n+1)):=le_max_left _ _
  unfold clippedWeight
  apply mul_le_mul
  · exact pow_le_pow_right₀ (by norm_num) hz
  · calc
      _ ≤ ∏_j∈Finset.range (inactive d),max 1 (c*Real.sqrt (n+1)):=by
        apply Finset.prod_le_prod₀
        · intro j hj;exact le_trans zero_le_one (le_max_left _ _)
        · intro j hj
          apply max_le_max le_rfl
          apply mul_le_mul_of_nonneg_left _ hc
          apply Real.sqrt_le_sqrt
          have hj':=Finset.mem_range.mp hj
          exact_mod_cast (show j+1 ≤ n+1 by omega)
      _ = (max 1 (c*Real.sqrt (n+1)))^(inactive d):=by simp
      _ ≤ _:=pow_le_pow_right₀ hM hi
  · exact Finset.prod_nonneg (fun j _=>le_trans zero_le_one (le_max_left _ _))
  · positivity
end WP
namespace WP
open Set
lemma harmonic_comparison_proof (P : PsiTheory) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, ∀ d : List ℕ, d.length = n → Stable g n →
    d.sum ≤ dimension g n → ∀ Y ∈ Set.Icc 0 y₀,
      -C*(Real.log (complexity g n+1))^2 ≤ Real.log (ratio P g d Y) ∧
      Real.log (ratio P g d Y) ≤ C*Real.sqrt (complexity g n) := by
  obtain ⟨c,B,hc,hB,hLower⟩:=comparison_lower P
  obtain ⟨c₀,hc₀,hUp⟩:=comparison_upper P
  obtain ⟨U,hU,hUpper⟩:=hUp (c₀/2) ⟨by positivity,by linarith⟩
  let V:ℝ:=(4:ℝ)^n*(max 1 ((c₀/2)*Real.sqrt (n+1)))^n
  have hV:0<V:=by dsimp[V];positivity
  let K:ℝ:=U*V
  have hK:0<K:=mul_pos hU hV
  let L:ℝ:=4*|Real.log c|+B*(2*n+1)
  let C:ℝ:=max L (U+|Real.log K|+1)
  have hC:0<C:=lt_of_lt_of_le (by positivity:0<U+|Real.log K|+1) (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro g d hlen hs hd Y hY
  have hs':Stable g d.length:=by simpa only [hlen] using hs
  have hd':d.sum ≤ dimension g d.length:=by simpa only [hlen] using hd
  have hn':1 ≤ d.length:=by omega
  have hh:1 ≤ complexity g n:=by unfold complexity;unfold Stable at hs;omega
  have hroot:1 ≤ Real.sqrt (complexity g n:ℝ):=by
    calc (1:ℝ)=Real.sqrt 1:=by norm_num
         _ ≤ _:=Real.sqrt_le_sqrt (by exact_mod_cast hh)
  let ell:ℝ:=Real.log (complexity g n+1)
  have hell:(1/2:ℝ) ≤ ell:=by
    have hhR:(2:ℝ) ≤ (complexity g n+1:ℕ):=by exact_mod_cast (show 2 ≤ complexity g n+1 by omega)
    have hl:=Real.log_le_log (by norm_num:0<(2:ℝ)) hhR
    dsimp[ell]
    push_cast at hl
    linarith [Real.log_two_gt_d9]
  have hell0:0 ≤ ell:=by linarith
  have hellsq:1 ≤ 4*ell^2:=by nlinarith
  have hellLin:ell ≤ 2*ell^2:=by nlinarith
  have hz:zeros d ≤ n:=by
    have hfilter:=List.length_filter_le (fun k:ℕ=>k=0) d
    simpa only [zeros,hlen] using hfilter
  have hzR:(zeros d:ℝ) ≤ n:=by exact_mod_cast hz
  have hl:=hLower g d hn' hs' hd' Y hY
  have hp:0<ratio P g d Y:=lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) hl
  have hlogL:=Real.log_le_log (mul_pos hc (Real.exp_pos _)) hl
  rw [Real.log_mul hc.ne' (Real.exp_ne_zero _),Real.log_exp] at hlogL
  have hzLin:(zeros d:ℝ)*ell ≤ 2*(n:ℝ)*ell^2:=by
    have ha:=mul_le_mul_of_nonneg_right hzR hell0
    have hb:=mul_le_mul_of_nonneg_left hellLin (Nat.cast_nonneg n:0 ≤ (n:ℝ))
    nlinarith
  have hcLin:|Real.log c| ≤ 4*|Real.log c| *ell^2:=by
    have ha:=mul_le_mul_of_nonneg_left hellsq (abs_nonneg (Real.log c))
    nlinarith
  have hBL:B*((zeros d:ℝ)+ell)*ell ≤ B*(2*(n:ℝ)+1)*ell^2:=by
    have ha:=mul_le_mul_of_nonneg_left hzLin hB.le
    nlinarith
  have hlow:-L*ell^2 ≤ Real.log (ratio P g d Y):=by
    dsimp[L]
    rw [hlen] at hlogL
    change Real.log c + -B*((zeros d:ℝ)+ell)*ell ≤ _ at hlogL
    nlinarith [neg_abs_le (Real.log c)]
  have hclip:clippedWeight (c₀/2) d ≤ V:=clippedWeight_fixed_length _ (by positivity) n d hlen
  have hu:=hUpper g d hn' hs' hd' Y hY
  have hupper:ratio P g d Y ≤ K*Real.exp (U*Real.sqrt (complexity g n)):=by
    rw [hlen] at hu
    have ha:=mul_le_mul_of_nonneg_left hclip hU.le
    have hb:=mul_le_mul_of_nonneg_right ha (Real.exp_pos (U*Real.sqrt (complexity g n))).le
    exact hu.trans hb
  have hlogU:=Real.log_le_log hp hupper
  rw [Real.log_mul hK.ne' (Real.exp_ne_zero _),Real.log_exp] at hlogU
  constructor
  · have hCL:L*ell^2 ≤ C*ell^2:=mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ell)
    have hneg:-C*ell^2 ≤ -L*ell^2:=by nlinarith
    exact hneg.trans hlow
  · have hlogK:Real.log K ≤ |Real.log K| *Real.sqrt (complexity g n):=by
      nlinarith [le_abs_self (Real.log K),abs_nonneg (Real.log K)]
    have hsmall:U+|Real.log K| ≤ C:=by
      have hc:=le_max_right L (U+|Real.log K|+1)
      dsimp[C]
      linarith
    have hmul:=mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg (complexity g n:ℝ))
    nlinarith
end WP
