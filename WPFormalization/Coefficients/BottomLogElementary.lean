import WPFormalization.Coefficients.SaddleActionRegularity
/-! Exact degree and logarithmic estimates for the original C.23 error scale. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set
lemma one_boundary_saddle_defect_degree_bound (g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    (complexity g 1:ℝ)*(3/2-((3*g-2-k:ℕ):ℝ)/complexity g 1)^2 ≤ (k+1:ℝ)^2/g:=by
  have hhc:complexity g 1=2*g-1:=by unfold complexity;omega
  have hN:3*complexity g 1=2*(3*g-2-k)+2*k+1:=by unfold complexity;omega
  have hgR:0 < (g:ℝ):=by exact_mod_cast (show 0 < g by omega)
  have hH:0 < (complexity g 1:ℝ):=by exact_mod_cast (show 0 < complexity g 1 by unfold complexity;omega)
  have hgH:(g:ℝ) ≤ complexity g 1:=by exact_mod_cast (show g ≤ complexity g 1 by unfold complexity;omega)
  have hNr:(3:ℝ)*complexity g 1=2*((3*g-2-k:ℕ):ℝ)+2*k+1:=by exact_mod_cast hN
  have he:3/2-((3*g-2-k:ℕ):ℝ)/complexity g 1=((k:ℝ)+1/2)/complexity g 1:=by
    apply (eq_div_iff hH.ne').mpr
    field_simp
    nlinarith only[hNr]
  rw[he]
  calc
    _ = ((k:ℝ)+1/2)^2/complexity g 1:=by field_simp <;>ring
    _ ≤ (k+1:ℝ)^2/complexity g 1:=div_le_div_of_nonneg_right
      (by nlinarith only[show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k]) hH.le
    _ ≤ _:=div_le_div_of_nonneg_left (sq_nonneg _) hgR hgH

lemma genus_log_complexity_bounds (g:ℕ)(hg:1 ≤ g):
    0 ≤ Real.log ((complexity g 1:ℝ)+1) ∧
    Real.log ((complexity g 1:ℝ)+1) ≤ 2*Real.log ((g:ℝ)+1) ∧
    (Real.log ((complexity g 1:ℝ)+1))^2 ≤ 4*(Real.log ((g:ℝ)+1))^2:=by
  have hh:(complexity g 1:ℝ)+1=2*(g:ℝ):=by
    have H:complexity g 1+1=2*g:=by unfold complexity;omega
    exact_mod_cast H
  have hgR:(1:ℝ) ≤ g:=by exact_mod_cast hg
  have h0:0 ≤ Real.log ((complexity g 1:ℝ)+1):=Real.log_nonneg (by linarith only[hh,hgR])
  have h1:0 ≤ Real.log ((g:ℝ)+1):=Real.log_nonneg (by linarith only[hgR])
  have h2:Real.log ((complexity g 1:ℝ)+1) ≤ 2*Real.log ((g:ℝ)+1):=by
    rw[show 2*Real.log ((g:ℝ)+1)=Real.log (((g:ℝ)+1)^2) by rw[Real.log_pow];norm_num]
    exact Real.log_le_log (by positivity) (by nlinarith only[hh,hgR])
  exact ⟨h0,h2,by nlinarith only[h0,h1,h2]⟩
lemma absorb_bottom_log_errors (A B D E:ℝ)(hA:0 < A)(hB:0 < B)(hD:0 < D)(hE:0 ≤ E):
    ∃C:ℝ,0 < C∧∀x t:ℝ,2 ≤ x →0 ≤ t →
      E+2*A*Real.log x+4*D*(Real.log x)^2+B*t ≤ C*(Real.log x)^2+C*t:=by
  let L:ℝ:=Real.log 2
  have hL:0 < L:=Real.log_pos (by norm_num)
  let F:ℝ:=E/L^2+2*A/L+4*D
  let C:ℝ:=F+B+1
  have hF:0 < F:=by dsimp[F];positivity
  have hC:0 < C:=by dsimp[C];positivity
  refine ⟨C,hC,?_⟩
  intro x t hx ht
  have hxl: L ≤ Real.log x:=Real.log_le_log (by norm_num) hx
  have hx0:0 ≤ Real.log x:=hL.le.trans hxl
  have hs:L^2 ≤ (Real.log x)^2:=by nlinarith only[hL,hxl]
  have he:E ≤ (E/L^2)*(Real.log x)^2:=by
    calc
      _ = (E/L^2)*L^2:=by field_simp
      _ ≤ _:=mul_le_mul_of_nonneg_left hs (by positivity)
  have ha:2*A*Real.log x ≤ (2*A/L)*(Real.log x)^2:=by
    calc
      _ = (2*A/L)*(L*Real.log x):=by field_simp
      _ ≤ _:=mul_le_mul_of_nonneg_left
        (by nlinarith only[mul_le_mul_of_nonneg_right hxl hx0]) (by positivity)
  have hf:F*(Real.log x)^2 ≤ C*(Real.log x)^2:=
    mul_le_mul_of_nonneg_right (by dsimp[C];linarith only[hB]) (sq_nonneg _)
  have hb:B*t ≤ C*t:=mul_le_mul_of_nonneg_right (by dsimp[C];linarith only[hF]) ht
  dsimp[F] at hf
  nlinarith only[he,ha,hf,hb]
end WP.Coefficients
