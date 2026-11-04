import WPFormalization.Coefficients.OneBoundaryBracketModel
import WPFormalization.External.FixedCusps
import WPFormalization.Volumes.OriginNormalization
/-! A weak one-boundary scale upper bound from the already registered classical fixed-cusp theorem. The unknown classical leading constant is retained. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set
lemma oneBoundaryBracketScale_pos (g:ℕ)(hg:1 ≤ g):0 < oneBoundaryBracketScale g:=by
  have hh:0 < complexity g 1:=by unfold complexity;omega
  have hhR:(0:ℝ) < complexity g 1:=by exact_mod_cast hh
  unfold oneBoundaryBracketScale
  exact mul_pos (mul_pos (sq_pos_of_pos Real.pi_pos) (Real.Gamma_pos_of_pos hhR)) (by positivity)

lemma fixedCuspLeadingScale_one_le_bracket_scale (g:ℕ)(hg:1 ≤ g):
    fixedCuspLeadingScale g 1 ≤ oneBoundaryBracketScale g/Real.pi^2:=by
  have hc:(complexity g 1:ℝ)=2*(g:ℝ)-1:=by
    unfold complexity
    rw[Nat.cast_sub (by omega)]
    push_cast
    ring
  have hn:complexity g 1-1=2*g-2:=by unfold complexity;omega
  have hgR:(1:ℝ) ≤ g:=by exact_mod_cast hg
  have hπ:(1:ℝ) ≤ Real.pi:=by linarith only[Real.pi_gt_three]
  have hs:1 ≤ Real.sqrt (Real.pi*g):=Real.one_le_sqrt.mpr (one_le_mul_of_one_le_of_one_le hπ hgR)
  have he:oneBoundaryBracketScale g/Real.pi^2=
      Real.Gamma (2*(g:ℝ)-1)*(4*Real.pi^2)^(2*g-2):=by
    unfold oneBoundaryBracketScale
    rw[hc,hn]
    field_simp
  rw[fixedCuspLeadingScale_one_gamma g hg,he]
  have hh:0 < 2*(g:ℝ)-1:=by linarith only[hgR]
  exact div_le_self (mul_nonneg (Real.Gamma_pos_of_pos hh).le (by positivity)) hs

lemma volume_one_le_bracket_scale (P:PsiTheory):
    ∃C:ℝ,0 < C∧∃G:ℕ,∀g:ℕ,G ≤ g →1 ≤ g →
      volumeModel P g 1 ≤ C*oneBoundaryBracketScale g:=by
  obtain ⟨c,hc,hall⟩:=External.fixed_cusps_universal_leading P
  obtain ⟨C,hC,G,hb⟩:=hall 1
  refine ⟨(c+C)/Real.pi^2,by positivity,G,?_⟩
  intro g hg hg1
  have hgR:(1:ℝ) ≤ g:=by exact_mod_cast hg1
  have hg0:(0:ℝ) < g:=by linarith only[hgR]
  have hS:0 < fixedCuspLeadingScale g 1:=by
    rw[fixedCuspLeadingScale_one_gamma g hg1]
    have hh:0 < 2*(g:ℝ)-1:=by linarith only[hgR]
    exact div_pos (mul_pos (Real.Gamma_pos_of_pos hh) (by positivity)) (by positivity)
  have hbound:|volumeModel P g 1/fixedCuspLeadingScale g 1-c| ≤ C/g:=by
    simpa only[fixedCuspLeadingScale] using hb g hg
  have hratio:volumeModel P g 1/fixedCuspLeadingScale g 1 ≤ c+C:=by
    have hu:volumeModel P g 1/fixedCuspLeadingScale g 1-c ≤ C/g:=
      (le_abs_self _).trans hbound
    have hd:C/(g:ℝ) ≤ C:=div_le_self hC.le hgR
    linarith only[hu,hd]
  calc
    _ ≤ (c+C)*fixedCuspLeadingScale g 1:=(div_le_iff₀ hS).mp hratio
    _ ≤ (c+C)*(oneBoundaryBracketScale g/Real.pi^2):=
      mul_le_mul_of_nonneg_left (fixedCuspLeadingScale_one_le_bracket_scale g hg1) (by positivity)
    _ = _:=by ring
end WP.Coefficients
