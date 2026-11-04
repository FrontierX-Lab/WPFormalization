import WPFormalization.Marked.LogGrowth
import WPFormalization.Comparison.HarmonicProof
/-! Actual logarithmic normalization uniformly for marking counts p <= M sqrt(h). The constants do not depend on p, g, degrees, or the closed physical parameter. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace WP
open Set
lemma clippedWeight_polynomial_length (c : ℝ) (hc : 0 ≤ c) (p : ℕ)
    (d : List ℕ) (hd : d.length = p) :
    clippedWeight c d ≤ (4*(1+c)*((p:ℝ)+1))^p := by
  have hp : 1 ≤ (p:ℝ)+1 := by linarith [show (0:ℝ) ≤ p from Nat.cast_nonneg p]
  have hroot : Real.sqrt ((p:ℝ)+1) ≤ (p:ℝ)+1 :=
    Real.sqrt_le_self_iff.mpr (Or.inr hp)
  have hmax : max 1 (c*Real.sqrt ((p:ℝ)+1)) ≤ (1+c)*((p:ℝ)+1) := by
    apply max_le
    · nlinarith [mul_nonneg hc (show 0 ≤ (p:ℝ)+1 by positivity)]
    · have he := mul_le_mul_of_nonneg_left hroot hc
      nlinarith
  calc
    _ ≤ (4:ℝ)^p*(max 1 (c*Real.sqrt (p+1)))^p := clippedWeight_fixed_length c hc p d hd
    _ ≤ (4:ℝ)^p*((1+c)*((p:ℝ)+1))^p := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hmax p
    _ = _ := by rw [←mul_pow]; congr 1;ring

lemma ratio_growing_markings_log_envelope (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ g p : ℕ, 1 ≤ p → Stable g p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀ d : List ℕ, d.length=p →
      d.sum ≤ dimension g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      |Real.log (ratio P g d Y)| ≤ C*(
        Real.sqrt (complexity g p:ℝ)*Real.log ((complexity g p:ℝ)+1)+
        (Real.log ((complexity g p:ℝ)+1))^2+1) := by
  obtain ⟨c,B,hc,hB,hLower⟩ := comparison_lower P
  obtain ⟨c₀,hc₀,hUp⟩ := comparison_upper P
  obtain ⟨U,hU,hUpper⟩ := hUp (c₀/2) ⟨by positivity,by linarith⟩
  let V : ℝ := 4*(1+c₀/2)
  have hV : 1 ≤ V := by dsimp [V];linarith
  have hlV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hlM : 0 ≤ Real.log (M+1) := Real.log_nonneg (by linarith)
  let a : ℝ := |Real.log U|
  let b : ℝ := M*(Real.log V+Real.log (M+1))+U
  let C : ℝ := |Real.log c|+B*M+B+a+2*b+M+1
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 < b := by dsimp [b];positivity
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro g p hp hs hpM d hd had Y hY
  let h : ℝ := complexity g p
  let q : ℝ := Real.sqrt h
  let l : ℝ := Real.log (h+1)
  let F : ℝ := q*l+l^2+1
  have hh1 : 1 ≤ h := by dsimp [h];exact_mod_cast (show 1 ≤ complexity g p by unfold Stable at hs;unfold complexity;omega)
  have hh : 0 < h := by linarith
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : 1 ≤ q := by dsimp [q];exact Real.one_le_sqrt.mpr hh1
  have hql : q ≤ h := by dsimp [q];exact Real.sqrt_le_self_iff.mpr (Or.inr hh1)
  have hl : 1/2 ≤ l := by
    have he := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ) ≤ h+1)
    dsimp [l]
    linarith [Real.log_two_gt_d9]
  have hl0 : 0 ≤ l := by linarith
  have hql0 : 0 ≤ q*l := mul_nonneg hq0 hl0
  have hF1 : 1 ≤ F := by dsimp [F];nlinarith [sq_nonneg l]
  have hqlF : q*l ≤ F := by dsimp [F];nlinarith [sq_nonneg l]
  have hl2F : l^2 ≤ F := by dsimp [F];nlinarith
  have hqF : q ≤ 2*F := by
    have he := mul_le_mul_of_nonneg_left hl hq0
    nlinarith
  have hn : 1 ≤ d.length := by omega
  have hst : Stable g d.length := by simpa only [hd] using hs
  have had' : d.sum ≤ dimension g d.length := by simpa only [hd] using had
  have hz : (zeros d:ℝ) ≤ p := by
    exact_mod_cast (show zeros d ≤ p by simpa [zeros,hd] using List.length_filter_le (fun k:ℕ=>k=0) d)
  have hlo := hLower g d hn hst had' Y hY
  have hR : 0 < ratio P g d Y := lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) hlo
  have hloglo := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hlo
  rw [Real.log_mul hc.ne' (Real.exp_ne_zero _),Real.log_exp] at hloglo
  rw [hd] at hloglo
  change Real.log c + -B*((zeros d:ℝ)+l)*l ≤ _ at hloglo
  have hzl : (zeros d:ℝ)*l ≤ M*(q*l) := by
    have he := mul_le_mul_of_nonneg_right (hz.trans hpM) hl0
    nlinarith
  have hlo' : -(|Real.log c|+B*M+B)*F ≤ Real.log (ratio P g d Y) := by
    have he0 := mul_le_mul_of_nonneg_left hF1 (abs_nonneg (Real.log c))
    have he1 := mul_le_mul_of_nonneg_left hqlF (mul_nonneg hB.le hM.le)
    have he2 := mul_le_mul_of_nonneg_left hl2F hB.le
    have he3 := mul_le_mul_of_nonneg_left hzl hB.le
    nlinarith [neg_abs_le (Real.log c)]
  have hclip := clippedWeight_polynomial_length (c₀/2) (by positivity) p d hd
  have hupper := (hUpper g d hn hst had' Y hY).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hclip hU.le) (Real.exp_pos _).le)
  rw [hd] at hupper
  have hpositive : 0 < U*(V*((p:ℝ)+1))^p*Real.exp (U*q) := by dsimp [V];positivity
  have hlogup := Real.log_le_log hR hupper
  change Real.log (ratio P g d Y) ≤ Real.log (U*(V*((p:ℝ)+1))^p*Real.exp (U*q)) at hlogup
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp,
    Real.log_mul hU.ne' (by dsimp [V];positivity),Real.log_pow,
    Real.log_mul (by dsimp [V];positivity) (by positivity)] at hlogup
  have hp1 : (p:ℝ)+1 ≤ (M+1)*(h+1) := by
    have he := mul_le_mul_of_nonneg_left hql hM.le
    change (p:ℝ) ≤ M*q at hpM
    nlinarith
  have hlogp : Real.log ((p:ℝ)+1) ≤ Real.log (M+1)+l := by
    have he := Real.log_le_log (by positivity : 0 < (p:ℝ)+1) hp1
    rwa [Real.log_mul (by positivity) (by positivity)] at he
  have hlp0 : 0 ≤ Real.log ((p:ℝ)+1) := Real.log_nonneg (by linarith [show (0:ℝ) ≤ p from Nat.cast_nonneg p])
  have hpterm : (p:ℝ)*(Real.log V+Real.log ((p:ℝ)+1)) ≤
      M*q*(Real.log V+Real.log (M+1)+l) := by
    apply mul_le_mul hpM (by linarith)
    · exact add_nonneg hlV hlp0
    · exact mul_nonneg hM.le hq0
  have hlogup' : Real.log (ratio P g d Y) ≤ a+b*q+M*(q*l) := by
    dsimp [a,b]
    nlinarith only [hlogup,hpterm,le_abs_self (Real.log U)]
  have hup' : Real.log (ratio P g d Y) ≤ (a+2*b+M)*F := by
    have he0 := mul_le_mul_of_nonneg_left hF1 ha
    have he1 := mul_le_mul_of_nonneg_left hqF hb.le
    have he2 := mul_le_mul_of_nonneg_left hqlF hM.le
    nlinarith
  apply abs_le.mpr
  constructor
  · have hCF : (|Real.log c|+B*M+B)*F ≤ C*F := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      dsimp [C]
      linarith
    change -(C*F) ≤ _
    linarith
  · have hCF : (a+2*b+M)*F ≤ C*F := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      dsimp [C]
      nlinarith only [abs_nonneg (Real.log c),hB,hM]
    exact hup'.trans hCF
end WP

namespace WP
open Set
lemma W_growing_markings_log_envelope (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℕ, ∀ g p : ℕ, 1 ≤ p → Stable g p →
      H ≤ complexity g p → (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) →
      ∀ Y ∈ Icc (0:ℝ) y₀,
      |Real.log (W P g p Y)-Real.log (Real.Gamma (complexity g p))+
        (complexity g p:ℝ)*Real.log (A Y)| ≤ C*(
          Real.sqrt (complexity g p:ℝ)*Real.log ((complexity g p:ℝ)+1)+
          (Real.log ((complexity g p:ℝ)+1))^2+1) := by
  obtain ⟨Cr,hCr,hRatio⟩ := ratio_growing_markings_log_envelope P M hM
  obtain ⟨Cc,hCc,Hc,hCentral⟩ := Analysis.harmonicCoeff_central_log_bound (M/2) (by positivity)
  obtain ⟨N,hN⟩ := exists_nat_gt (M^2+1)
  refine ⟨Cr+Cc+1,by positivity,max Hc N,?_⟩
  intro g p hp hs hH hpM Y hY
  let h : ℕ := complexity g p
  have hhN : N ≤ h := (le_max_right _ _).trans hH
  have hhC : Hc ≤ h := (le_max_left _ _).trans hH
  have hh1 : 1 ≤ h := by dsimp [h];unfold complexity;unfold Stable at hs;omega
  have hhR1 : (1:ℝ) ≤ h := by exact_mod_cast hh1
  have hh : 0 < h := by omega
  have hhR : (0:ℝ) ≤ h := Nat.cast_nonneg _
  have hlarge : M^2+1 < (h:ℝ) := hN.trans_le (by exact_mod_cast hhN)
  have hg : 2 ≤ g := by
    by_contra hg
    have hhp : h ≤ p := by dsimp [h];unfold complexity;omega
    have he : (h:ℝ) ≤ M*Real.sqrt (h:ℝ) := (by exact_mod_cast hhp : (h:ℝ) ≤ p) |>.trans hpM
    nlinarith only [he,hlarge,Real.sq_sqrt hhR,sq_nonneg (Real.sqrt (h:ℝ)-M)]
  have hm : |(dimension g p:ℝ)-3*(h:ℝ)/2| ≤ (M/2)*Real.sqrt (h:ℝ) := by
    dsimp [h]
    rw [marked_dimension_offset g p hg,abs_div,abs_neg,abs_of_nonneg (Nat.cast_nonneg p)]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith only [hpM]
  have hcent := hCentral h hhC hh Y hY (dimension g p) hm
  have hrat := hRatio g p hp hs hpM (List.replicate p 0) (by simp) (by simp) Y hY
  let F : ℝ := Real.sqrt (h:ℝ)*Real.log ((h:ℝ)+1)+(Real.log ((h:ℝ)+1))^2+1
  have hl0 : 0 ≤ Real.log (h:ℝ) := Real.log_nonneg hhR1
  have hl1 : 0 ≤ Real.log ((h:ℝ)+1) := Real.log_nonneg (by linarith)
  have hl : Real.log (h:ℝ) ≤ Real.log ((h:ℝ)+1) := Real.log_le_log (by positivity) (by linarith)
  have hprod : 0 ≤ Real.sqrt (h:ℝ)*Real.log ((h:ℝ)+1) := mul_nonneg (Real.sqrt_nonneg _) hl1
  have hF : 1 ≤ F := by dsimp [F];nlinarith only [hprod,sq_nonneg (Real.log ((h:ℝ)+1))]
  have hlog : |Real.log (h:ℝ)|/2 ≤ F := by
    rw [abs_of_nonneg hl0]
    dsimp [F]
    nlinarith only [hl,hprod,sq_nonneg (Real.log ((h:ℝ)+1)-1)]
  rw [W_log_harmonic_decomposition P g p hp hs Y hY]
  have heq : Real.log (ratio P g (List.replicate p 0) Y)+
      Real.log (harmonicCoeff Y h (dimension g p))+(h:ℝ)*Real.log (barH Y 1).re=
      Real.log (ratio P g (List.replicate p 0) Y)+
      (Real.log (harmonicCoeff Y h (dimension g p))+(h:ℝ)*Real.log (barH Y 1).re+Real.log (h:ℝ)/2)-Real.log (h:ℝ)/2 := by ring
  change |Real.log (ratio P g (List.replicate p 0) Y)+Real.log (harmonicCoeff Y h (dimension g p))+
    (h:ℝ)*Real.log (barH Y 1).re| ≤ (Cr+Cc+1)*F
  rw [heq]
  calc
    _ ≤ |Real.log (ratio P g (List.replicate p 0) Y)|+
        |Real.log (harmonicCoeff Y h (dimension g p))+(h:ℝ)*Real.log (barH Y 1).re+Real.log (h:ℝ)/2|+
        |Real.log (h:ℝ)|/2 := by
      calc
        _ ≤ |Real.log (ratio P g (List.replicate p 0) Y)+
            (Real.log (harmonicCoeff Y h (dimension g p))+(h:ℝ)*Real.log (barH Y 1).re+Real.log (h:ℝ)/2)|+
            |Real.log (h:ℝ)/2| := abs_sub _ _
        _ ≤ _ := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)];gcongr;exact abs_add_le _ _
    _ ≤ Cr*F+Cc+F := add_le_add (add_le_add hrat hcent) hlog
    _ ≤ _ := by nlinarith only [mul_nonneg hCc.le (sub_nonneg.mpr hF)]
end WP
