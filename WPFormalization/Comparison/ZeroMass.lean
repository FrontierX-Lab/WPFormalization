import WPFormalization.Weighted.LinearMass
import WPFormalization.Intersection.TerminalLower
/-! The true all-zero linear mass and its cumulative-loss bound.
Positive coefficient convolution proves the preceding harmonic coefficient
is at most its successor. The exact mass identity then gives mass at least
2/3, logarithmic loss at most n/h, and the explicit exponential lower bound. -/
noncomputable section
namespace WP
open Set
lemma harmonicCoeff_pred_le (Y:ℝ)(hY:Y∈Icc 0 y₀)(h m:ℕ)(hh:2 ≤ h):
    harmonicCoeff Y (h-1) m ≤ harmonicCoeff Y h m := by
  have he:=harmonicCoeff_convolution Y hY (h-1) 1 m
  have hsucc:h-1+1=h:=by omega
  rw[hsucc] at he
  have h0:harmonicCoeff Y 1 0=1:=Analysis.harmonicCoeff_one_zero Y hY
  have hs:harmonicCoeff Y (h-1) m*harmonicCoeff Y 1 (m-m) ≤
      ∑k∈Finset.range (m+1),harmonicCoeff Y (h-1) k*harmonicCoeff Y 1 (m-k):=by
    apply Finset.single_le_sum (a:=m) (f:=fun k=>harmonicCoeff Y (h-1) k*harmonicCoeff Y 1 (m-k))
    · intro k hk
      exact mul_nonneg (harmonicCoeff_pos Y (h-1) k (by omega) hY).le (harmonicCoeff_pos Y 1 (m-k) (by omega) hY).le
    · simp
  simpa only[Nat.sub_self,h0,mul_one,he] using hs
lemma zeroMass_basic_lower (Y:ℝ)(hY:Y∈Icc 0 y₀)(g n:ℕ)(hg:2 ≤ g)(hn:1 ≤ n):
    1-(n:ℝ)/(3*((complexity g n:ℝ)-1)) ≤ zeroLinearMass Y g n := by
  let h:=complexity g n
  let m:=dimension g n
  let t:=harmonicCoeff Y (h-1) m/harmonicCoeff Y h m
  have hh:2 ≤ h:=by dsimp[h];unfold complexity;omega
  have hhr:(2:ℝ) ≤ h:=by exact_mod_cast hh
  have hden:0 < 3*((h:ℝ)-1):=by linarith
  have ht0:0 ≤ t:=by dsimp[t];exact div_nonneg (harmonicCoeff_pos Y (h-1) m (by omega) hY).le (harmonicCoeff_pos Y h m (by omega) hY).le
  have ht1:t ≤ 1:=by
    dsimp[t]
    exact (div_le_one (harmonicCoeff_pos Y h m (by omega) hY)).mpr (harmonicCoeff_pred_le Y hY h m hh)
  have he:zeroLinearMass Y g n=1+((3-(n:ℝ))/(3*((h:ℝ)-1)))*t:=by
    rw[zero_mass_defect Y g n hg hn hY]
    dsimp[t,h,m]
    ring
  rw[he]
  change 1-(n:ℝ)/(3*((h:ℝ)-1)) ≤ _
  by_cases hsmall:(n:ℝ) ≤ 3
  · have hc:0 ≤ (3-(n:ℝ))/(3*((h:ℝ)-1)):=div_nonneg (by linarith) hden.le
    have hp:=mul_nonneg hc ht0
    have hn0:0 ≤ (n:ℝ)/(3*((h:ℝ)-1)):=by positivity
    linarith
  · have hc:(3-(n:ℝ))/(3*((h:ℝ)-1)) ≤ 0:=div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
    have hp:=mul_le_mul_of_nonpos_left ht1 hc
    have hd3:0 ≤ 3/(3*((h:ℝ)-1)):=by positivity
    linarith [show (3-(n:ℝ))/(3*((h:ℝ)-1))=3/(3*((h:ℝ)-1))-(n:ℝ)/(3*((h:ℝ)-1)) by ring]
lemma zeroMass_two_thirds (Y:ℝ)(hY:Y∈Icc 0 y₀)(g n:ℕ)(hg:2 ≤ g)(hn:1 ≤ n):
    (2/3:ℝ) ≤ zeroLinearMass Y g n := by
  have hh:2 ≤ complexity g n:=by unfold complexity;omega
  have hhR:(2:ℝ) ≤ complexity g n:=by exact_mod_cast hh
  have hden:0 < 3*((complexity g n:ℝ)-1):=by linarith
  have hn':(n:ℝ) ≤ (complexity g n:ℝ)-1:=by
    have hc:n+1 ≤ complexity g n:=by unfold complexity;omega
    have hcr:(n:ℝ)+1 ≤ complexity g n:=by exact_mod_cast hc
    linarith
  have hfrac:(n:ℝ)/(3*((complexity g n:ℝ)-1)) ≤ 1/3:=by
    apply (div_le_iff₀ hden).mpr
    linarith
  linarith[zeroMass_basic_lower Y hY g n hg hn]
lemma log_mass_defect_generic (s n h:ℝ)(hs:(2/3:ℝ) ≤ s)(hn:0 ≤ n)(hh:2 ≤ h)
    (hdef:1-n/(3*(h-1)) ≤ s): -Real.log (min s 1) ≤ n/h := by
  have hs0:0 < s:=by linarith
  have hh0:0 < h:=by linarith
  have hd:0 < 3*(h-1):=by linarith
  by_cases hs1:s ≤ 1
  · rw[min_eq_left hs1]
    have hlog:=Real.log_le_sub_one_of_pos (inv_pos.mpr hs0)
    rw[Real.log_inv] at hlog
    have hinv:s⁻¹ ≤ 3/2:=by
      rw[inv_eq_one_div]
      apply (div_le_iff₀ hs0).mpr
      linarith
    have hc:=mul_le_mul_of_nonneg_right hinv (sub_nonneg.mpr hs1)
    have he:s⁻¹*(1-s)=s⁻¹-1:=by field_simp
    rw[he] at hc
    have hA:-Real.log s ≤ n/(2*(h-1)):=by
      have hmult:=mul_le_mul_of_nonneg_left hdef (by norm_num : (0:ℝ) ≤ 3/2)
      have hrat:(3/2:ℝ)*(n/(3*(h-1)))=n/(2*(h-1)):=by
        field_simp [ne_of_gt (show 0 < h-1 by linarith)]
        <;> ring
      nlinarith
    apply hA.trans
    apply div_le_div_of_nonneg_left hn hh0
    linarith
  · rw[min_eq_right (le_of_not_ge hs1),Real.log_one,neg_zero]
    exact div_nonneg hn hh0.le
lemma zeroMass_exp_lower (Y:ℝ)(hY:Y∈Icc 0 y₀)(g n:ℕ)(hg:2 ≤ g)(hn:1 ≤ n):
    Real.exp (-(n:ℝ)/(complexity g n:ℝ)) ≤ zeroLinearMass Y g n := by
  have hh:2 ≤ complexity g n:=by unfold complexity;omega
  have hhR:(2:ℝ) ≤ complexity g n:=by exact_mod_cast hh
  have hlog:=log_mass_defect_generic (zeroLinearMass Y g n) n (complexity g n)
    (zeroMass_two_thirds Y hY g n hg hn) (Nat.cast_nonneg _) hhR (zeroMass_basic_lower Y hY g n hg hn)
  have hs:0 < min (zeroLinearMass Y g n) 1:=lt_min (by linarith[zeroMass_two_thirds Y hY g n hg hn]) zero_lt_one
  calc _ ≤ Real.exp (Real.log (min (zeroLinearMass Y g n) 1)):=Real.exp_le_exp.mpr (by simpa only[neg_div,neg_neg] using neg_le_neg hlog)
       _=min (zeroLinearMass Y g n) 1:=Real.exp_log hs
       _ ≤ _:=min_le_left _ _
end WP
