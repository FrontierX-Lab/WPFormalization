import WPFormalization.Coefficients.AdjacentSaddleCalibration
import WPFormalization.Coefficients.AdjacentDiscreteSecants
import WPFormalization.Coefficients.BracketAdjacentStructure
/-! The actual finite-h saddle prediction is calibrated uniformly in degree.
The original trigonometric saddle equals the original infimum mean saddle;
no m=N-k term is replaced, so bounded positive codimension is retained. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology

def adjacentSaddlePrediction (g k:ℕ) : ℝ :=
  (2*(k:ℝ)+3)*(complexity g 1:ℝ)*
    saddleChi (((3*g-2-k:ℕ):ℝ)/(complexity g 1:ℝ))

lemma chi_sampled_log_calibration : ∃C:ℝ,0<C ∧∀g k:ℝ,1 ≤ g→1 ≤ k→k ≤ 3*g-2→
    |Real.log (((2*k+3)*(2*g-1)*saddleChi ((3*g-2-k)/(2*g-1)))/g^2)-
      Real.log (adjacentProfileQ (k/g))| ≤ C/k := by
  obtain ⟨C,hC,hχ⟩ := saddleChi_log_lipschitz
  refine ⟨5+6*C,by positivity,?_⟩
  intro g k hg hk hk3
  have hgp:0<g := by linarith
  have hkp:0<k := by linarith
  let h:ℝ:=2*g-1
  let u:ℝ:=(3*g-2-k)/h
  let v:ℝ:=(3-k/g)/2
  have hhp:0<h := by dsimp[h];linarith
  have hgh:g ≤ h := by dsimp[h];linarith
  have hu:u∈Icc (0:ℝ) (3/2) := by
    refine ⟨div_nonneg (by linarith) hhp.le,(div_le_iff₀ hhp).mpr ?_⟩
    dsimp[h];linarith
  have hv:v∈Icc (0:ℝ) (3/2) := by
    refine ⟨by dsimp[v];apply div_nonneg _ (by norm_num);apply sub_nonneg.mpr;(apply (div_le_iff₀ hgp).mpr);linarith,?_⟩
    dsimp[v]
    have hk0:0 ≤ k/g:=div_nonneg hkp.le hgp.le
    linarith
  have hχu:0<saddleChi u := lt_of_lt_of_le (by norm_num:(0:ℝ)<1/5) (saddleChi_lower _ hu)
  have hχv:0<saddleChi v := lt_of_lt_of_le (by norm_num:(0:ℝ)<1/5) (saddleChi_lower _ hv)
  have hdiff:|u-v| ≤ 2/g := by
    have he:u-v=-(g+k)/(2*g*h) := by
      dsimp[u,v]
      field_simp [hhp.ne']
      dsimp[h]
      ring
    rw [he,abs_div,abs_neg,abs_of_pos (by linarith:0<g+k),abs_of_pos (by positivity:0<2*g*h)]
    have he1:(g+k)/(2*g) ≤ 2 := (div_le_iff₀ (by positivity:0<2*g)).mpr (by linarith)
    calc _ = ((g+k)/(2*g))/h := by ring
         _  ≤  2/h := div_le_div_of_nonneg_right he1 hhp.le
         _  ≤  _ := div_le_div_of_nonneg_left (by norm_num) hgp hgh
  have hχbound : |Real.log (saddleChi u)-Real.log (saddleChi v)| ≤ 2*C/g := by
    have he := hχ v hv u hu
    exact he.trans (by calc C*|u-v| ≤ C*(2/g):=mul_le_mul_of_nonneg_left hdiff hC.le
                           _ = _ := by ring)
  let x:ℝ:=(2*k+3)/(2*k)
  let y:ℝ:=h/(2*g)
  have hx:0<x := div_pos (by positivity) (by positivity)
  have hy:0<y := div_pos hhp (by positivity)
  have hx1:1 ≤ x := (le_div_iff₀ (by positivity:0<2*k)).mpr (by linarith)
  have hy1:y ≤ 1 := (div_le_one (by positivity:0<2*g)).mpr (by dsimp[h];linarith)
  have hlogx:|Real.log x| ≤ 2/k := by
    have he := Real.log_le_sub_one_of_pos hx
    rw[abs_of_nonneg (Real.log_nonneg hx1)]
    calc _  ≤  x-1 := he
         _  ≤  2/k := by dsimp[x];apply (le_div_iff₀ hkp).mpr;field_simp;linarith
  have hlogy:|Real.log y| ≤ 1/g := by
    have he := Analysis.log_ordered_difference_le y 1 hy hy1
    rw[Real.log_one,zero_sub] at he
    rw[abs_of_nonpos (Real.log_nonpos hy.le hy1)]
    calc _  ≤  (1-y)/y := he.2
         _ = 1/h := by dsimp[y,h];field_simp <;>ring
         _  ≤  _ := div_le_div_of_nonneg_left (by norm_num) hgp hgh
  have hfactor : ((2*k+3)*(2*g-1)*saddleChi ((3*g-2-k)/(2*g-1)))/g^2=
      adjacentProfileQ (k/g)*x*y*(saddleChi u/saddleChi v) := by
    change ((2*k+3)*h*saddleChi u)/g^2=_
    dsimp[adjacentProfileQ,x,y]
    change ((2*k+3)*h*saddleChi u)/g^2=4*(k/g)*saddleChi v*((2*k+3)/(2*k))*(h/(2*g))*(saddleChi u/saddleChi v)
    field_simp [hgp.ne',hkp.ne',hχv.ne']
    <;> ring
  have hq:0<adjacentProfileQ (k/g) := adjacentProfileQ_pos _
    ⟨div_pos hkp hgp,(div_le_iff₀ hgp).mpr (by linarith)⟩
  rw[hfactor,Real.log_mul (mul_pos (mul_pos hq hx) hy).ne' (div_pos hχu hχv).ne',
    Real.log_mul (mul_pos hq hx).ne' hy.ne',Real.log_mul hq.ne' hx.ne',Real.log_div hχu.ne' hχv.ne']
  calc _ = |Real.log x+Real.log y+(Real.log (saddleChi u)-Real.log (saddleChi v))| := by congr 1;ring
       _  ≤  |Real.log x|+|Real.log y|+|Real.log (saddleChi u)-Real.log (saddleChi v)| :=
         (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
       _  ≤  2/k+1/g+2*C/g := add_le_add (add_le_add hlogx hlogy) hχbound
       _  ≤  (5+6*C)/k := by
         have he:1/g ≤ 3/k := (div_le_div_iff₀ hgp hkp).mpr (by linarith)
         have heC:=mul_le_mul_of_nonneg_left he (show 0 ≤ 2*C by positivity)
         calc _ = 2/k+1/g+(2*C)*(1/g) := by ring
              _  ≤  2/k+3/k+(2*C)*(3/k) := add_le_add (add_le_add_right he _) heC
              _ = _ := by ring
lemma adjacent_complexity_one_cast (g:ℕ)(hg:1 ≤ g) : (complexity g 1:ℝ)=2*(g:ℝ)-1 := by
  have he:complexity g 1+1=2*g := by unfold complexity;omega
  have her:(complexity g 1:ℝ)+1=2*(g:ℝ) := by exact_mod_cast he
  linarith

lemma adjacent_deficit_one_cast (g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2) :
    ((3*g-2-k:ℕ):ℝ)=3*(g:ℝ)-2-k := by
  rw[Nat.cast_sub hk,Nat.cast_sub (by omega)]
  push_cast;rfl

lemma adjacent_mean_parameter_mem (g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2) :
    (((3*g-2-k:ℕ):ℝ)/(complexity g 1:ℝ))∈Icc (0:ℝ) (3/2) := by
  have hgR:(1:ℝ) ≤ g := by exact_mod_cast hg
  have hh:0<(complexity g 1:ℝ) := by rw[adjacent_complexity_one_cast g hg];linarith
  refine ⟨div_nonneg (Nat.cast_nonneg _) hh.le,(div_le_iff₀ hh).mpr ?_⟩
  rw[adjacent_complexity_one_cast g hg,adjacent_deficit_one_cast g k hg hk]
  nlinarith [Nat.cast_nonneg (α:=ℝ) k]

lemma adjacentSaddlePrediction_eq_weight (g k:ℕ)(hg:1 ≤ g)(hk:k<3*g-2) :
    adjacentSaddlePrediction g k=oneBoundaryRatioWeight g k/((trigSaddle g k)^2/2) := by
  have ht:=(trig_saddle_spec g k hg hk).1
  have htp:0<trigSaddle g k:=ht.1
  have hz:0<(trigSaddle g k)^2/2 := by positivity
  have hh:0<(complexity g 1:ℝ) := by exact_mod_cast (show 0<complexity g 1 by unfold complexity;omega)
  have hs:=saddleChi_mul_saddleZeta _ (adjacent_mean_parameter_mem g k hg hk.le)
  rw[←trigSaddle_square_saddleZeta g k hg hk] at hs
  apply (eq_div_iff hz.ne').mpr
  unfold adjacentSaddlePrediction oneBoundaryRatioWeight
  have he:=congrArg (fun q:ℝ=>q*(complexity g 1:ℝ)*(2*(k:ℝ)+3)) hs
  field_simp [hh.ne'] at he
  nlinarith only [he]

lemma adjacentSaddlePrediction_pos (g k:ℕ)(hg:1 ≤ g)(hk:k<3*g-2) :
    0<adjacentSaddlePrediction g k := by
  rw[adjacentSaddlePrediction_eq_weight g k hg hk]
  exact div_pos (oneBoundaryRatioWeight_pos g k hk) (by have ht:0<trigSaddle g k:=(trig_saddle_spec g k hg hk).1.1;positivity)

lemma adjacentSaddlePrediction_log_calibration : ∃C:ℝ,0<C ∧∀g k:ℕ,1 ≤ g→1 ≤ k→k<3*g-2→
    |Real.log (adjacentSaddlePrediction g k/(g:ℝ)^2)-Real.log (adjacentProfileQ ((k:ℝ)/g))| ≤ C/k := by
  obtain ⟨C,hC,hcal⟩:=chi_sampled_log_calibration
  refine ⟨C,hC,?_⟩
  intro g k hg hk hkN
  have hgR:(1:ℝ) ≤ g := by exact_mod_cast hg
  have hkR:(1:ℝ) ≤ k := by exact_mod_cast hk
  have hkNR:(k:ℝ) ≤ 3*(g:ℝ)-2 := by
    have he:(k:ℝ) ≤ ((3*g-2:ℕ):ℝ) := by exact_mod_cast hkN.le
    rw[Nat.cast_sub (by omega)] at he
    push_cast at he
    exact he
  have he:=hcal g k hgR hkR hkNR
  simpa only[adjacentSaddlePrediction,adjacent_complexity_one_cast g hg,adjacent_deficit_one_cast g k hg hkN.le] using he

lemma adjacentError_eq_prediction (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k<3*g-2) :
    adjacentError P g k=|((mixedJ P g k/mixedJ P g (k+1))/adjacentSaddlePrediction g k)-1| := by
  have ht:=(trig_saddle_spec g k hg hk).1
  have hw:oneBoundaryRatioWeight g k≠0 := (oneBoundaryRatioWeight_pos g k hk).ne'
  unfold adjacentError
  rw[boundaryA_adjacent_eq_four_bracketAdjacentRatio,bracketAdjacentRatio_eq_mixedJ P g k hg hk,
    adjacentSaddlePrediction_eq_weight g k hg hk]
  congr 1
  field_simp [Real.pi_ne_zero,ht.1.ne',hw]
  <;> ring

lemma adjacentError_eq_exp_log_prediction (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k<3*g-2) :
    adjacentError P g k=|Real.exp (adjacentLogRatio P g k-Real.log (adjacentSaddlePrediction g k/(g:ℝ)^2))-1| := by
  have hgR:0<(g:ℝ) := by exact_mod_cast (show 0<g by omega)
  have hq:0< mixedJ P g k/mixedJ P g (k+1) :=
    div_pos (mixedJ_pos_admissible P g k hg hk.le) (mixedJ_pos_admissible P g (k+1) hg (by omega))
  have hp:0<adjacentSaddlePrediction g k := adjacentSaddlePrediction_pos g k hg hk
  rw[adjacentError_eq_prediction P g k hg hk,adjacentLogRatio,Real.exp_sub,
    Real.exp_log (div_pos hq (sq_pos_of_pos hgR)),Real.exp_log (div_pos hp (sq_pos_of_pos hgR))]
  congr 1
  field_simp
  <;> ring


end WP.Coefficients
