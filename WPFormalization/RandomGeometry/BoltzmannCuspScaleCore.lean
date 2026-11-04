import WPFormalization.Tight.ConnectedScale
import WPFormalization.Tight.ConnectedPoissonScale

noncomputable section
namespace WP.BoltzmannCusp
open Set
lemma density_relative_log_scale (l m:ℝ) (hl:0≤l) (hm:0 ≤ m)
    (he:|(1+l)/(1+m)-1|≤1/2) :
    |Real.log (tightScale l)-Real.log (tightScale m)|≤4*|(1+l)/(1+m)-1| := by
  have hd : 0<1+m := by linarith
  have hmin : 0<1+min l m := by have := le_min hl hm;linarith
  have hrel : (1+l)/(1+m)-1=(l-m)/(1+m) := by field_simp;ring
  have ha : |l-m|≤(1+m)/2 := by
    rw [hrel,abs_div,abs_of_pos hd] at he
    nlinarith [(div_le_iff₀ hd).mp he]
  have hlow : (1+m)/2≤1+min l m := by
    have hh := (abs_sub_le_iff.mp ha).2
    rcases le_total l m with hlm | hml
    · rw [min_eq_left hlm];linarith
    · rw [min_eq_right hml];linarith
  have hc := TightConnected.tightScale_log_comparison l m hl hm
  calc
    |Real.log (tightScale l)-Real.log (tightScale m)|≤2*|l-m|/(1+min l m) := hc
    _≤4*(|l-m|/(1+m)) := by
      apply (div_le_iff₀ hmin).mpr
      have hu : 0≤|l-m|/(1+m) := div_nonneg (abs_nonneg _) hd.le
      have hh := mul_le_mul_of_nonneg_left hlow (show 0≤4*(|l-m|/(1+m)) by positivity)
      have hid : 4*(|l-m|/(1+m))*((1+m)/2)=2*|l-m| := by field_simp;ring
      rw [hid] at hh
      exact hh
    _=4*|(1+l)/(1+m)-1| := by rw [hrel,abs_div,abs_of_pos hd]
end WP.BoltzmannCusp
namespace WP.BoltzmannCusp
lemma density_relative_scale (l m:ℝ) (hl:0≤l) (hm:0 ≤ m)
    (he:|(1+l)/(1+m)-1|≤1/4) :
    |tightScale l/tightScale m-1|≤8*|(1+l)/(1+m)-1| := by
  have ha:=TightConnected.tightScale_pos l hl
  have hb:=TightConnected.tightScale_pos m hm
  have hh:=density_relative_log_scale l m hl hm (he.trans (by norm_num))
  have heq : tightScale l/tightScale m=Real.exp (Real.log (tightScale l)-Real.log (tightScale m)) := by
    rw [Real.exp_sub,Real.exp_log ha,Real.exp_log hb]
  rw [heq]
  have hle : |Real.log (tightScale l)-Real.log (tightScale m)|≤1 := by linarith
  exact (Real.abs_exp_sub_one_le hle).trans (by linarith)
end WP.BoltzmannCusp
