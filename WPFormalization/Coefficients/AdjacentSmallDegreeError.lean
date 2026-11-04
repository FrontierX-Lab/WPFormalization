import WPFormalization.Coefficients.BracketSmallDegreeRate
import WPFormalization.Coefficients.AdjacentSaddleCalibration
/-! The original actual adjacentError has uniform g^(-1/8) decay through the full small-degree range. The true trigonometric saddle is retained. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
lemma adjacentError_eq_bracketRatio (P:PsiTheory)(g k:ℕ):
    adjacentError P g k=|(bracketAdjacentRatio P g k)*(trigSaddle g k)^2/Real.pi^2-1|:=by
  unfold adjacentError
  rw[boundaryA_adjacent_eq_four_bracketAdjacentRatio]
  congr 1
  rw[div_div_eq_mul_div]
  field_simp
  <;>ring

lemma adjacentError_small_degree_rate (P:PsiTheory):
    ∃C:ℝ,0 < C∧∃G:ℕ,∀g:ℕ,G ≤ g →∀k:ℕ,k < 3*g-2 →(k:ℝ) ≤ (g:ℝ)^(3/4:ℝ) →
      adjacentError P g k ≤ C*(g:ℝ)^(-1/8:ℝ):=by
  obtain ⟨C,hC,G,hρ⟩:=bracketAdjacentRatio_small_degree_rate P
  refine ⟨C+20/Real.pi^2,by positivity,max G 1,?_⟩
  intro g hg k hk hsmall
  have hgG:G ≤ g:=(le_max_left _ _).trans hg
  have hg1:1 ≤ g:=(le_max_right _ _).trans hg
  have hgR:(1:ℝ) ≤ g:=by exact_mod_cast hg1
  have hg0:0 < (g:ℝ):=zero_lt_one.trans_le hgR
  have hρb:=hρ g hgG k hsmall
  have hcal:=trigSaddle_square_endpoint_bound g k hg1 hk
  have ht:=(trig_saddle_spec g k hg1 hk).1
  have htsq:0 ≤ (trigSaddle g k)^2/Real.pi^2:=by positivity
  have htsq1:(trigSaddle g k)^2/Real.pi^2 ≤ 1:=by
    apply (div_le_one (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith only[ht.1,ht.2,Real.pi_pos]
  have hpow:(g:ℝ)^(-1/4:ℝ) ≤ (g:ℝ)^(-1/8:ℝ):=
    Real.rpow_le_rpow_of_exponent_le hgR (by norm_num)
  have hkg:((k:ℝ)+1)/g ≤ 2*(g:ℝ)^(-1/8:ℝ):=by
    have hp:1 ≤ (g:ℝ)^(3/4:ℝ):=Real.one_le_rpow hgR (by norm_num)
    have hnum:(k:ℝ)+1 ≤ 2*(g:ℝ)^(3/4:ℝ):=by linarith only[hsmall,hp]
    have H:=div_le_div_of_nonneg_right hnum hg0.le
    have he:2*(g:ℝ)^(3/4:ℝ)/g=2*(g:ℝ)^(-1/4:ℝ):=by
      calc
        _ = 2*((g:ℝ)^(3/4:ℝ)/(g:ℝ)^((1:ℝ))):=by rw[Real.rpow_one];ring
        _ = 2*(g:ℝ)^((3/4:ℝ)-1):=by rw[Real.rpow_sub hg0]
        _ = _:=by norm_num
    rw[he] at H
    exact H.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hcal2:|(trigSaddle g k)^2/Real.pi^2-1| ≤ (20/Real.pi^2)*(g:ℝ)^(-1/8:ℝ):=by
    have H:=mul_le_mul_of_nonneg_left hkg (show 0 ≤ 10/Real.pi^2 by positivity)
    simp only[div_eq_mul_inv] at hcal H ⊢
    nlinarith only[hcal,H]
  have hη:|bracketAdjacentRatio P g k-1| ≤ C*(g:ℝ)^(-1/8:ℝ):=by
    simpa only[abs_of_nonneg hρb.1] using hρb.2
  have hprod:|(bracketAdjacentRatio P g k-1)*((trigSaddle g k)^2/Real.pi^2)| ≤
      C*(g:ℝ)^(-1/8:ℝ):=by
    rw[abs_mul,abs_of_nonneg htsq]
    exact (mul_le_of_le_one_right (abs_nonneg _) htsq1).trans hη
  rw[adjacentError_eq_bracketRatio]
  have he:(bracketAdjacentRatio P g k)*(trigSaddle g k)^2/Real.pi^2-1=
      (bracketAdjacentRatio P g k-1)*((trigSaddle g k)^2/Real.pi^2)+
      ((trigSaddle g k)^2/Real.pi^2-1):=by ring
  rw[he]
  exact (abs_add_le _ _).trans (by nlinarith only[hprod,hcal2])
end WP.Coefficients
