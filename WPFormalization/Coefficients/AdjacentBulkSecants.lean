import WPFormalization.Coefficients.DegreeProfileRegularity
import WPFormalization.Coefficients.AdjacentDiscreteSecants
import WPFormalization.Statements.LogarithmicComparison
import WPFormalization.Coefficients.TopAnchorProof
/-! Quantitative secants of the actual degree coefficients, including every
bounded positive codimension at the top. Constants precede all genus, degree
and integer secant lengths. The exact top two mixed intersections supply the
truncated-right-secant case; no endpoint approximation is assumed. -/
noncomputable section
namespace WP.Coefficients
open Set

lemma finite_secant_tracking (l g r A R Gm G0 Gp fm f0 fp s q : ℝ)
    (hl:0<l) (hg:0<g) (hr:l=g*r)
    (hA:0 ≤ A) (hR:0 ≤ R)
    (hm:|Gm-g*fm|  ≤ A) (h0:|G0-g*f0|  ≤ A) (hp:|Gp-g*fp|  ≤ A)
    (hfm:|f0-fm+r*q|  ≤ R) (hfp:|fp-f0+r*q|  ≤ R)
    (hlo:(Gm-G0)/l ≤ s) (hup:s ≤ (G0-Gp)/l) :
    |s-q|  ≤ (2*A+g*R)/l := by
  have hm' := abs_le.mp hm
  have h0' := abs_le.mp h0
  have hp' := abs_le.mp hp
  have hfm' := abs_le.mp hfm
  have hfp' := abs_le.mp hfp
  have hfmlo := mul_le_mul_of_nonneg_left hfm'.1 hg.le
  have hfmhi := mul_le_mul_of_nonneg_left hfm'.2 hg.le
  have hfplo := mul_le_mul_of_nonneg_left hfp'.1 hg.le
  have hfphi := mul_le_mul_of_nonneg_left hfp'.2 hg.le
  have hlo' := (div_le_iff₀ hl).mp hlo
  have hup' := (le_div_iff₀ hl).mp hup
  rw [abs_le]
  constructor
  · rw [←neg_div]
    apply (div_le_iff₀ hl).mpr
    nlinarith [congrArg (fun x:ℝ=>x*q) hr]
  · apply (le_div_iff₀ hl).mpr
    nlinarith [congrArg (fun x:ℝ=>x*q) hr]

lemma degree_secant_scale_bound (D C g k l:ℝ)
    (hD:0<D)(hC:0<C)(hgr:0<g)(hkr:0<k)(hlr:0<l)(hkg:k≤3*g) :
    (2*(D*Real.sqrt g)+g*((2/(k/g)+C)*(l/g)^2))/l ≤
      (2*D+2+3*C)*(Real.sqrt g/l+l/k) := by
  have hratio : (g*((2/(k/g)+C)*(l/g)^2))/l=2*l/k+C*l/g := by field_simp <;> ring
  rw [add_div,hratio]
  have ht : l/g≤3*(l/k) := by
    calc _ ≤ l/(k/3) := div_le_div_of_nonneg_left hlr.le (by positivity) (by linarith)
         _ = _ := by ring
  have hcoef := mul_le_mul_of_nonneg_left ht hC.le
  have hpos1 : 0≤Real.sqrt g/l := by positivity
  have hpos2 : 0≤l/k := by positivity
  calc _ = 2*D*(Real.sqrt g/l)+2*(l/k)+C*(l/g) := by ring
       _ ≤ 2*D*(Real.sqrt g/l)+2*(l/k)+C*(3*(l/k)) := add_le_add_right hcoef _
       _ ≤ _ := by nlinarith only [mul_nonneg hD.le hpos2,mul_nonneg hC.le hpos1,hpos1]

lemma adjacentLogRatio_left_secant (P:PsiTheory) (g k l:ℕ) (hg:1≤g)
    (hl:1≤l)(hlk:l≤k)(hk:k<3*g-2) :
    (logComparisonG P g (k-l)-logComparisonG P g k)/(l:ℝ)≤adjacentLogRatio P g k := by
  have hlp:(0:ℝ)<l := by exact_mod_cast (show 0<l by omega)
  apply (div_le_iff₀ hlp).mpr
  have ht := finite_telescope_sub (logComparisonG P g) (k-l) l
  rw [Nat.sub_add_cancel hlk] at ht
  rw [←ht]
  calc _ = ∑i∈Finset.range l,adjacentLogRatio P g (k-l+i) := by
         apply Finset.sum_congr rfl
         intro i hi
         exact logComparisonG_increment P g (k-l+i) hg (by have hi':=Finset.mem_range.mp hi;omega)
       _ ≤ ∑i∈Finset.range l,adjacentLogRatio P g k := by
         apply Finset.sum_le_sum
         intro i hi
         apply adjacentLogRatio_monotone P g hg (by have hi':=Finset.mem_range.mp hi;change k-l+i<3*g-2;omega) hk
         have hi':=Finset.mem_range.mp hi
         omega
       _ = _ := by simp;ring

lemma adjacentLogRatio_left_bulk_bound (P:PsiTheory) :
    ∃E:ℝ,0<E ∧∀g:ℕ,1≤g→∀k l:ℕ,1≤l→2*l≤k→k<3*g-2→
      Real.log (adjacentProfileQ ((k:ℝ)/g))-E*(Real.sqrt g/l+(l:ℝ)/k)≤adjacentLogRatio P g k := by
  obtain ⟨D,hD,hmodel⟩ := logarithmic_comparison P
  obtain ⟨C,hC,hsec⟩ := logDegreeProfile_secant_remainder
  refine ⟨2*D+2+3*C,by positivity,?_⟩
  intro g hg k l hl hlk hk
  have hgr:(0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hkr:(0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hlr:(0:ℝ)<l := by exact_mod_cast (show 0<l by omega)
  have hk3:(k:ℝ)<3*g := by exact_mod_cast (show k<3*g by omega)
  have h2lk:2*(l:ℝ)≤k := by exact_mod_cast hlk
  let α:ℝ := (k:ℝ)/g
  let a:ℝ := ((k:ℝ)-l)/g
  let r:ℝ := (l:ℝ)/g
  have hα:α∈Ioo (0:ℝ) 3 := ⟨div_pos hkr hgr,(div_lt_iff₀ hgr).mpr hk3⟩
  have ha:a∈Ioo (0:ℝ) 3 := by
    refine ⟨div_pos (by linarith) hgr,(div_lt_iff₀ hgr).mpr ?_⟩
    linarith
  have haα:a≤α := div_le_div_of_nonneg_right (by linarith) hgr.le
  have hhalf:α/2≤a := by
    dsimp[α,a];rw[div_div]
    apply (div_le_div_iff₀ (by positivity:0<(g:ℝ)*2) hgr).mpr
    nlinarith
  have hr:0<r := div_pos hlr hgr
  have hadiff:α-a=r := by dsimp[α,a,r];ring
  have harem:|logDegreeProfile α-logDegreeProfile a+r*Real.log (adjacentProfileQ α)|≤(2/α+C)*r^2 := by
    have he:=hsec α hα a α ha hα haα hhalf
    rw[abs_of_nonpos (sub_nonpos.mpr haα),show -(a-α)=r by linarith,sub_self,abs_zero,max_eq_left hr.le,hadiff] at he
    simpa only[pow_two,mul_assoc] using he
  have hc:((k-l:ℕ):ℝ)=(k:ℝ)-l := by rw[Nat.cast_sub (by omega)]
  have hm:=abs_le.mp (hmodel g hg (k-l) (by omega))
  rw[hc] at hm
  have h0:=abs_le.mp (hmodel g hg k hk.le)
  have hr0:=abs_le.mp harem
  have hmul:=mul_le_mul_of_nonneg_left hr0.2 hgr.le
  have hleft:=(div_le_iff₀ hlr).mp (adjacentLogRatio_left_secant P g k l hg hl (by omega) hk)
  have hbound:=degree_secant_scale_bound D C g k l hD hC hgr hkr hlr hk3.le
  have he:Real.log (adjacentProfileQ α)-(2*(D*Real.sqrt g)+(g:ℝ)*((2/α+C)*r^2))/l≤adjacentLogRatio P g k := by
    have hlrid:(l:ℝ)=(g:ℝ)*r := by dsimp[r];field_simp
    have ht : (Real.log (adjacentProfileQ α)-adjacentLogRatio P g k)*(l:ℝ) ≤
        2*(D*Real.sqrt g)+(g:ℝ)*((2/α+C)*r^2) := by
      nlinarith only [hm.1,h0.2,hmul,hleft,congrArg (fun x:ℝ=>x*Real.log (adjacentProfileQ α)) hlrid]
    have ht' := (le_div_iff₀ hlr).mpr ht
    linarith only [ht']
  exact (sub_le_sub_left hbound _).trans he

lemma adjacentLogRatio_bulk_secant_bound (P:PsiTheory) :
    ∃C:ℝ,0<C ∧ ∀g:ℕ,1 ≤ g→∀k l:ℕ,1 ≤ l→2*l ≤ k→k<3*g-2→k+l ≤ 3*g-2→
      |adjacentLogRatio P g k-Real.log (adjacentProfileQ ((k:ℝ)/g))|  ≤
        C*(Real.sqrt g/l+(l:ℝ)/k) := by
  obtain ⟨D,hD,hmodel⟩ := logarithmic_comparison P
  obtain ⟨C,hC,hsec⟩ := logDegreeProfile_secant_remainder
  let E:ℝ := 2*D+2+3*C
  have hE : 0<E := by dsimp[E];positivity
  refine ⟨E,hE,?_⟩
  intro g hg k l hl hlk hk hkl
  have hgr : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hkr : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hlr : (0:ℝ)<l := by exact_mod_cast (show 0<l by omega)
  have hcast : ((k-l:ℕ):ℝ)=(k:ℝ)-l := by rw[Nat.cast_sub (by omega)]
  have hcastkl : ((k+l:ℕ):ℝ)=(k:ℝ)+l := by push_cast;rfl
  have hN : (3*g-2:ℕ)<3*g := by omega
  have hk3 : (k:ℝ)<3*g := by exact_mod_cast (hk.trans hN)
  have hkl3 : (k:ℝ)+l<3*g := by exact_mod_cast (hkl.trans_lt hN)
  have h2lk : 2*(l:ℝ) ≤ k := by exact_mod_cast hlk
  let α:ℝ := (k:ℝ)/g
  let a:ℝ := ((k:ℝ)-l)/g
  let b:ℝ := ((k:ℝ)+l)/g
  let r:ℝ := (l:ℝ)/g
  have hα : α∈Ioo (0:ℝ) 3 := ⟨div_pos hkr hgr,(div_lt_iff₀ hgr).mpr hk3⟩
  have ha : a∈Ioo (0:ℝ) 3 := by
    refine ⟨div_pos (by linarith) hgr,(div_lt_iff₀ hgr).mpr ?_⟩
    linarith
  have hb : b∈Ioo (0:ℝ) 3 := ⟨div_pos (by linarith) hgr,(div_lt_iff₀ hgr).mpr hkl3⟩
  have haα : a ≤ α := div_le_div_of_nonneg_right (by linarith) hgr.le
  have hαb : α ≤ b := div_le_div_of_nonneg_right (by linarith) hgr.le
  have hhalf : α/2 ≤ a := by dsimp[α,a];rw[div_div];apply (div_le_div_iff₀ (by positivity:0<(g:ℝ)*2) hgr).mpr; nlinarith
  have hhalfα : α/2 ≤ α := by linarith [hα.1]
  have hxa : |a-α|=r := by
    rw [abs_of_nonpos (sub_nonpos.mpr haα)]
    dsimp[a,α,r];ring
  have hxb : |b-α|=r := by
    rw [abs_of_nonneg (sub_nonneg.mpr hαb)]
    dsimp[b,α,r];ring
  have hr : 0<r := div_pos hlr hgr
  let R:ℝ := (2/α+C)*r^2
  have hR : 0 ≤ R := mul_nonneg (add_nonneg (div_nonneg (by norm_num) hα.1.le) hC.le) (sq_nonneg _)
  have hmrem : |logDegreeProfile α-logDegreeProfile a+r*Real.log (adjacentProfileQ α)|  ≤ R := by
    have he := hsec α hα a α ha hα haα hhalf
    rw [hxa,sub_self,abs_zero,max_eq_left hr.le] at he
    have hma : α-a=r := by dsimp[α,a,r];ring
    rw [hma] at he
    simpa only [R,pow_two,mul_assoc] using he
  have hprem : |logDegreeProfile b-logDegreeProfile α+r*Real.log (adjacentProfileQ α)|  ≤ R := by
    have he := hsec α hα α b hα hb hαb hhalfα
    rw [sub_self,abs_zero,hxb,max_eq_right hr.le] at he
    have hmb : b-α=r := by dsimp[b,α,r];ring
    rw [hmb] at he
    simpa only [R,pow_two,mul_assoc] using he
  have hml := hmodel g hg (k-l) (by omega)
  have h0 := hmodel g hg k hk.le
  have hp := hmodel g hg (k+l) hkl
  rw [hcast] at hml
  rw [hcastkl] at hp
  have hdis := adjacentLogRatio_secants P g k l hg hl (by omega) hk hkl
  have he := finite_secant_tracking l g r (D*Real.sqrt g) R
    (logComparisonG P g (k-l)) (logComparisonG P g k) (logComparisonG P g (k+l))
    (logDegreeProfile a) (logDegreeProfile α) (logDegreeProfile b)
    (adjacentLogRatio P g k) (Real.log (adjacentProfileQ α)) hlr hgr
    (by dsimp[r];field_simp) (mul_nonneg hD.le (Real.sqrt_nonneg _)) hR hml h0 hp hmrem hprem hdis.1 hdis.2
  have hbound : (2*(D*Real.sqrt g)+(g:ℝ)*R)/l  ≤  E*(Real.sqrt g/l+(l:ℝ)/k) := by
    have hkg : (k:ℝ) ≤ 3*g := hk3.le
    have hratio : ((g:ℝ)*R)/(l:ℝ)=2*(l:ℝ)/k+C*(l:ℝ)/g := by
      dsimp[R,α,r]
      field_simp
      <;> ring
    rw [add_div,hratio]
    have ht : (l:ℝ)/g ≤ 3*((l:ℝ)/k) := by
      calc _ ≤ (l:ℝ)/((k:ℝ)/3) := div_le_div_of_nonneg_left hlr.le (by positivity) (by linarith)
           _ = _ := by ring
    have hcoef := mul_le_mul_of_nonneg_left ht hC.le
    have hpos1 : 0 ≤ Real.sqrt (g:ℝ)/l := by positivity
    have hpos2 : 0 ≤ (l:ℝ)/k := by positivity
    calc _ = 2*D*(Real.sqrt g/l)+2*((l:ℝ)/k)+C*((l:ℝ)/g) := by ring
         _ ≤ 2*D*(Real.sqrt g/l)+2*((l:ℝ)/k)+C*(3*((l:ℝ)/k)) := add_le_add_right hcoef _
         _ ≤ _ := by
           dsimp[E]
           nlinarith only [mul_nonneg hD.le hpos2,mul_nonneg hC.le hpos1,hpos1]
  exact he.trans hbound
lemma adjacentProfileQ_log_three_variation : ∃C:ℝ,0<C ∧∀α∈Ioo (0:ℝ) 3,
    |Real.log (adjacentProfileQ 3)-Real.log (adjacentProfileQ α)| ≤ (1/α+C)*(3-α) := by
  obtain ⟨C,hC,hχ⟩ := saddleChi_log_lipschitz
  refine ⟨C/2,by positivity,?_⟩
  intro α hα
  have hu:(3-α)/2∈Icc (0:ℝ) (3/2) := by constructor <;> linarith [hα.1,hα.2]
  have ha:0<saddleChi ((3-α)/2) := lt_of_lt_of_le (by norm_num:(0:ℝ)<1/5) (saddleChi_lower _ hu)
  have h0:0<saddleChi 0 := by rw[saddleChi_zero];norm_num
  have hq3 : Real.log (adjacentProfileQ 3)=Real.log 4+Real.log 3+Real.log (saddleChi 0) := by
    rw [adjacentProfileQ]
    norm_num only [sub_self,zero_div]
    rw [Real.log_mul (by norm_num) h0.ne']
    rw [show Real.log (12:ℝ)=Real.log 4+Real.log 3 from by
      rw [←Real.log_mul (by norm_num:(4:ℝ)≠0) (by norm_num:(3:ℝ)≠0)];norm_num]
  have hqa : Real.log (adjacentProfileQ α)=Real.log 4+Real.log α+Real.log (saddleChi ((3-α)/2)) := by
    rw [adjacentProfileQ,Real.log_mul (mul_pos (by norm_num) hα.1).ne' ha.ne',Real.log_mul (by norm_num) hα.1.ne']
  have hlog := Analysis.log_ordered_difference_le α 3 hα.1 hα.2.le
  have hchi := hχ ((3-α)/2) hu 0 ⟨le_rfl,by norm_num⟩
  have habs:|0-(3-α)/2|=(3-α)/2 := by rw[zero_sub,abs_neg,abs_of_nonneg (by linarith [hα.2])]
  rw [habs] at hchi
  rw [hq3,hqa]
  calc _ = |(Real.log 3-Real.log α)+(Real.log (saddleChi 0)-Real.log (saddleChi ((3-α)/2)))| := by congr 1;ring
       _ ≤ |Real.log 3-Real.log α|+|Real.log (saddleChi 0)-Real.log (saddleChi ((3-α)/2))| := abs_add_le _ _
       _ ≤ (3-α)/α+C*((3-α)/2) := add_le_add (by rw[abs_of_nonneg hlog.1];exact hlog.2) hchi
       _ = _ := by ring

lemma adjacentLogRatio_top_bound (P:PsiTheory) (g:ℕ) (hg:1≤g) :
    |adjacentLogRatio P g (3*g-3)-Real.log (adjacentProfileQ 3)| ≤ (12/5)/(g:ℝ) := by
  have hgr:(1:ℝ)≤g := by exact_mod_cast hg
  have hgp:(0:ℝ)<g := by linarith
  let q:ℝ := (12*(g:ℝ)^2-12*g+5)/(5*(g:ℝ)^2)
  have hq1:1≤q := by
    apply (le_div_iff₀ (by positivity:0<5*(g:ℝ)^2)).mpr
    have he : 0≤((g:ℝ)-1)*(7*g-5) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hqU:q≤12/5 := by
    apply (div_le_iff₀ (by positivity:0<5*(g:ℝ)^2)).mpr
    nlinarith
  have hqq:12/5-q≤(12/5)/(g:ℝ) := by
    dsimp [q]
    field_simp
    nlinarith [sq_nonneg (g:ℝ)]
  have hl := Analysis.log_ordered_difference_le q (12/5) (by linarith) hqU
  have hlog : |Real.log q-Real.log (12/5)|≤(12/5)/(g:ℝ) := by
    rw [abs_sub_comm,abs_of_nonneg hl.1]
    exact hl.2.trans ((div_le_self (sub_nonneg.mpr hqU) hq1).trans hqq)
  unfold adjacentLogRatio
  have hn:(3*g-3)+1=3*g-2 := by omega
  rw [hn,top_anchor_mixedJ_ratio P g hg,adjacentProfileQ_three]
  convert hlog using 1
  congr 2
  dsimp [q]
  ring

lemma adjacentLogRatio_full_bulk_secant_bound (P:PsiTheory) :
    ∃C:ℝ,0<C ∧∀g:ℕ,1≤g→∀k l:ℕ,1≤l→2*l≤k→k<3*g-2→
      |adjacentLogRatio P g k-Real.log (adjacentProfileQ ((k:ℝ)/g))| ≤
        C*(Real.sqrt g/l+(l:ℝ)/k) := by
  obtain ⟨Ci,hCi,hinterior⟩ := adjacentLogRatio_bulk_secant_bound P
  obtain ⟨Cl,hCl,hleft⟩ := adjacentLogRatio_left_bulk_bound P
  obtain ⟨Ct,hCt,htopvar⟩ := adjacentProfileQ_log_three_variation
  let C:ℝ := Ci+Cl+12+9*Ct
  have hC : 0<C := by dsimp[C];positivity
  refine ⟨C,hC,?_⟩
  intro g hg k l hl hlk hk
  have hgr:(0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hkr:(0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hlr:(1:ℝ)≤l := by exact_mod_cast hl
  have hscale:0≤Real.sqrt (g:ℝ)/l+(l:ℝ)/k := by positivity
  by_cases hkl:k+l≤3*g-2
  · exact (hinterior g hg k l hl hlk hk hkl).trans (mul_le_mul_of_nonneg_right (by dsimp[C];linarith) hscale)
  have hk3:(k:ℝ)<3*g := by exact_mod_cast (show k<3*g by omega)
  have hgap:3*(g:ℝ)-(k:ℝ)≤3*l := by
    have he : 3*g≤k+l+2 := by omega
    have her : 3*(g:ℝ)≤k+l+2 := by exact_mod_cast he
    linarith
  let α:ℝ := (k:ℝ)/g
  have hα:α∈Ioo (0:ℝ) 3 := ⟨div_pos hkr hgr,(div_lt_iff₀ hgr).mpr hk3⟩
  have hdiff:3-α≤3*((l:ℝ)/g) := by
    dsimp[α]
    calc _ = (3*(g:ℝ)-(k:ℝ))/g := by field_simp <;> ring
         _ ≤ (3*(l:ℝ))/g := div_le_div_of_nonneg_right hgap hgr.le
         _ = _ := by ring
  have hnorm := adjacentLogRatio_monotone P g hg hk
    (show 3*g-3∈Iio (3*g-2) by change 3*g-3<3*g-2;omega) (by omega)
  have htop := adjacentLogRatio_top_bound P g hg
  have hv := htopvar α hα
  have hupper : adjacentLogRatio P g k-Real.log (adjacentProfileQ α) ≤
      (12/5)/(g:ℝ)+(1/α+Ct)*(3-α) := by
    nlinarith only [hnorm,(le_abs_self _).trans htop,(le_abs_self _).trans hv]
  have hlg:(l:ℝ)/g≤3*((l:ℝ)/k) := by
    calc _ ≤ (l:ℝ)/((k:ℝ)/3) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
         _ = _ := by ring
  have h1g:1/(g:ℝ)≤3*((l:ℝ)/k) :=
    (div_le_div_of_nonneg_right hlr hgr.le).trans hlg
  have hfin : (12/5)/(g:ℝ)+(1/α+Ct)*(3-α) ≤ (12+9*Ct)*((l:ℝ)/k) := by
    have he := mul_le_mul_of_nonneg_left hdiff
      (show 0≤1/α+Ct from add_nonneg (div_nonneg (by norm_num) hα.1.le) hCt.le)
    have hCtlg := mul_le_mul_of_nonneg_left hlg (show 0≤3*Ct by positivity)
    have hconst := mul_le_mul_of_nonneg_left h1g (show 0≤(12/5:ℝ) by norm_num)
    have hratio : (1/α+Ct)*(3*((l:ℝ)/g))=3*((l:ℝ)/k)+3*Ct*((l:ℝ)/g) := by
      dsimp[α];field_simp <;> ring
    rw [hratio] at he
    have hbase:(12/5)/(g:ℝ)=(12/5)*(1/(g:ℝ)) := by ring
    rw [hbase]
    nlinarith only [he,hCtlg,hconst,show (0:ℝ)≤(l:ℝ)/k by positivity]
  rw [abs_le]
  constructor
  · have he := hleft g hg k l hl hlk hk
    have hc:Cl*(Real.sqrt (g:ℝ)/l+(l:ℝ)/k)≤C*(Real.sqrt g/l+(l:ℝ)/k) :=
      mul_le_mul_of_nonneg_right (by dsimp[C];linarith) hscale
    linarith only [he,hc]
  · calc _ ≤ (12/5)/(g:ℝ)+(1/α+Ct)*(3-α) := hupper
         _ ≤ (12+9*Ct)*((l:ℝ)/k) := hfin
         _ ≤ C*(Real.sqrt g/l+(l:ℝ)/k) := by
           have hpos1:0≤Real.sqrt (g:ℝ)/l := by positivity
           have hpos2:0≤(l:ℝ)/k := by positivity
           have hcc:12+9*Ct≤C := by dsimp[C];linarith
           exact (mul_le_mul_of_nonneg_right hcc hpos2).trans
             (mul_le_mul_of_nonneg_left (by linarith) hC.le)

end WP.Coefficients
