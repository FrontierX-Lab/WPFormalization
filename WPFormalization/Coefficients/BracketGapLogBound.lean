import WPFormalization.Coefficients.BracketGapPropagation
import WPFormalization.Analysis.FiniteLogRatioBlock
import WPFormalization.Statements.BottomLogBound
/-! The logarithmic cost of the genuine propagated bracket gap is controlled by the proved original C.23 bound. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients

lemma bracketAdjacentRatio_truncated_gap_log_bound (P:PsiTheory):
    ∃C:ℝ,0 < C∧∃G:ℕ,∀g:ℕ,G ≤ g →1 ≤ g →∀k:ℕ,2*(k+1) ≤ 3*g-2 →
      (min (bracketAdjacentRatio P g k-1) 1)^2*((k:ℝ)+1) ≤
        C*(Real.log ((g:ℝ)+1))^2+C*((k:ℝ)+1)^2/g:=by
  obtain ⟨C,hC,G,hb⟩:=bottom_log_bound P
  refine ⟨192*C,by positivity,G,?_⟩
  intro g hg hg1 k hk
  have hkN:k < 3*g-2:=by omega
  have hgR:0 < (g:ℝ):=by exact_mod_cast (show 0 < g by omega)
  let r:ℝ:=min (bracketAdjacentRatio P g k-1) 1
  have hr:0 ≤ r:=le_min (sub_nonneg.mpr (bracketAdjacentRatio_ge_one P g k hg1 hkN)) (by norm_num)
  have hr1:r ≤ 1:=min_le_right _ _
  have hgap:1+r ≤ bracketAdjacentRatio P g k:=by
    have H:=min_le_left (bracketAdjacentRatio P g k-1) 1
    dsimp[r]
    linarith only[H]
  let L:ℕ:=⌊r*((k:ℝ)+1)/12⌋₊+1
  have hfloor:(⌊r*((k:ℝ)+1)/12⌋₊:ℝ) ≤ r*((k:ℝ)+1)/12:=Nat.floor_le (by positivity)
  have hLlo:r*((k:ℝ)+1)/12 ≤ (L:ℝ):=by
    have H:=Nat.lt_floor_add_one (r*((k:ℝ)+1)/12)
    dsimp[L]
    push_cast
    exact H.le
  have hLhi:L ≤ k+1:=by
    have H:⌊r*((k:ℝ)+1)/12⌋₊ ≤ k:=by
      by_contra H
      have HN:k+1 ≤ ⌊r*((k:ℝ)+1)/12⌋₊:=by omega
      have HR:(k:ℝ)+1 ≤ (⌊r*((k:ℝ)+1)/12⌋₊:ℝ):=by exact_mod_cast HN
      have hm:=mul_le_mul_of_nonneg_right hr1 (show (0:ℝ) ≤ (k:ℝ)+1 by positivity)
      nlinarith only[hfloor,HR,hm,show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k]
    dsimp[L]
    omega
  have hLpos:1 ≤ L:=by dsimp[L];omega
  have hlast:k+L ≤ 3*g-2:=by omega
  have hpos:∀j:ℕ,j ≤ L →0 < bracketB P g (k+j):=by
    intro j hj
    exact bracketB_pos_admissible P g (k+j) hg1 (by omega)
  have hzero:0 < bracketB P g 0:=bracketB_pos_admissible P g 0 hg1 (by omega)
  have hstart:bracketB P g k ≤ bracketB P g 0:=by
    have H:=bracketB_le_volume_one P g k hg1 (by omega)
    have he:volumeModel P g 1=bracketB P g 0:=by simp[volumeModel,bracketB]
    rwa[he] at H
  have hlocal:∀i:ℕ,i < L →1+r/2 ≤ bracketB P g (k+i)/bracketB P g (k+i+1):=by
    intro i hi
    have hiN:i ≤ ⌊r*((k:ℝ)+1)/12⌋₊:=by dsimp[L] at hi;omega
    have hiR:(i:ℝ) ≤ r*((k:ℝ)+1)/12:=
      (show (i:ℝ) ≤ (⌊r*((k:ℝ)+1)/12⌋₊:ℝ) by exact_mod_cast hiN).trans hfloor
    have H:=bracketAdjacentRatio_gap_propagates P g k (k+i) r hg1 (by omega) (by omega) hr hr1
      (by push_cast;nlinarith only[hiR]) hgap
    simpa only[bracketAdjacentRatio,Nat.add_assoc] using H
  have hcost:=Analysis.finite_log_ratio_block_bound (bracketB P g) k L r hr hr1 hpos hzero hstart hlocal
  have he:bracketB P g 0=volumeModel P g 1:=by simp[volumeModel,bracketB]
  rw[he] at hcost
  have hC23:=(hb g hg (k+L) hlast).2
  have hLsmall:((k+L:ℕ):ℝ)+1 ≤ 2*((k:ℝ)+1):=by
    have H:((L:ℕ):ℝ) ≤ (k:ℝ)+1:=by exact_mod_cast hLhi
    push_cast
    linarith only[H]
  have hsquare:(((k+L:ℕ):ℝ)+1)^2 ≤ 4*((k:ℝ)+1)^2:=by
    have H:0 ≤ ((k+L:ℕ):ℝ)+1:=by positivity
    nlinarith only[hLsmall,H]
  have hq:=mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsquare hgR.le) hC.le
  have hrlow:=mul_le_mul_of_nonneg_left hLlo hr
  have hCpos:0 ≤ C*(Real.log ((g:ℝ)+1))^2:=mul_nonneg hC.le (sq_nonneg _)
  dsimp[r] at hcost hrlow
  simp only[div_eq_mul_inv] at hcost hC23 hq hrlow ⊢
  nlinarith only[hcost,hC23,hq,hrlow,hCpos]
end WP.Coefficients
