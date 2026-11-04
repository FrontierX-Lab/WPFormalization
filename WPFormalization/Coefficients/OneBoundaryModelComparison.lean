import WPFormalization.Coefficients.TopAnchorProof
import WPFormalization.Coefficients.UniformSaddleBasic
import WPFormalization.Statements.HarmonicComparison
import WPFormalization.Marked.Positivity
/-! The exact one-boundary mixed-intersection model and its genuine all-degree logarithmic comparison. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set

def oneBoundaryModelJ (g k:ℕ):ℝ:=
  (3:ℝ)^(complexity g 1)*Real.Gamma (complexity g 1)/4^g *
    ((3*g-2-k).factorial:ℝ)*unscaledCoeff (complexity g 1) (3*g-2-k)/(oddFactorial k:ℝ)

lemma oneBoundaryModelJ_pos (g k:ℕ)(hg:1 ≤ g):0 < oneBoundaryModelJ g k:=by
  have hh:0 < complexity g 1:=by unfold complexity;omega
  have hhR:(0:ℝ) < complexity g 1:=by exact_mod_cast hh
  have hG:=Real.Gamma_pos_of_pos hhR
  have hc:=unscaledCoeff_pos (complexity g 1) (3*g-2-k) hh
  have ho:(0:ℝ) < oddFactorial k:=by exact_mod_cast oddFactorial_pos k
  unfold oneBoundaryModelJ
  positivity

lemma mixedJ_div_oneBoundaryModelJ (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    mixedJ P g k/oneBoundaryModelJ g k=ratio P g [k] 0:=by
  have hdef:deficit g [k]=3*g-2-k:=by simp only[deficit,List.length_singleton,List.sum_singleton,dimension];omega
  have hh:0 < complexity g 1:=by unfold complexity;omega
  have hhR:(0:ℝ) < complexity g 1:=by exact_mod_cast hh
  have hG:(Real.Gamma (complexity g 1):ℝ)≠0:=(Real.Gamma_pos_of_pos hhR).ne'
  have hc:unscaledCoeff (complexity g 1) (3*g-2-k)≠0:=(unscaledCoeff_pos _ _ hh).ne'
  have ho:(oddFactorial k:ℝ)≠0:=by exact_mod_cast oddFactorial_ne_zero k
  have hf:((3*g-2-k).factorial:ℝ)≠0:=by exact_mod_cast Nat.factorial_ne_zero _
  have hp:(3:ℝ)^(complexity g 1)≠0:=by positivity
  have h4:(4:ℝ)^g≠0:=by positivity
  have hr:(r 0)^(3*g-2-k)≠0:=pow_ne_zero _ (r_pos 0 ⟨le_rfl,y₀_pos⟩).ne'
  rw[top_anchor_mixedJ_shifted P g k hg]
  simp only[oneBoundaryModelJ,ratio,model,normalized,
    show (0:ℝ)≠y₀ from ne_of_lt y₀_pos,ite_false,a_zero,one_pow,one_mul,
    List.length_singleton,hdef,harmonicCoeff_zero_unscaled]
  field_simp
  <;>ring

lemma oneBoundaryModelJ_top (g:ℕ):oneBoundaryModelJ g (3*g-2)=
    (3:ℝ)^(complexity g 1)*Real.Gamma (complexity g 1)/4^g/(oddFactorial (3*g-2):ℝ):=by
  simp only[oneBoundaryModelJ,Nat.sub_self,Nat.factorial_zero,Nat.cast_one,mul_one,unscaledCoeff_zero]
end WP.Coefficients
namespace WP.Analysis
lemma log_sq_le_sixteen_sqrt (x:ℝ)(hx:1 ≤ x):
    (Real.log x)^2 ≤ 16*Real.sqrt x:=by
  have hx0:0 ≤ x:=zero_le_one.trans hx
  have hl:=Real.log_le_rpow_div hx0 (by norm_num:(0:ℝ) < 1/4)
  have hp0:0 ≤ x^(1/4:ℝ):=Real.rpow_nonneg hx0 _
  have hlog0:0 ≤ Real.log x:=Real.log_nonneg hx
  have hs:(x^(1/4:ℝ))^2=Real.sqrt x:=by
    calc
      _=x^((1/4:ℝ)*(2:ℕ)):=(Real.rpow_mul_natCast hx0 _ 2).symm
      _=x^(1/2:ℝ):=by norm_num
      _=_:=(Real.sqrt_eq_rpow x).symm
  nlinarith only[hl,hp0,hlog0,hs]
end WP.Analysis
namespace WP.Coefficients
lemma oneBoundaryModelJ_log_comparison (P:PsiTheory):
    ∃C:ℝ,0 < C∧∀g:ℕ,1 ≤ g →∀k:ℕ,k ≤ 3*g-2 →
      |Real.log (mixedJ P g k/oneBoundaryModelJ g k)| ≤ C*Real.sqrt g:=by
  obtain ⟨C,hC,hb⟩:=harmonic_comparison P 1 (by norm_num)
  refine ⟨32*C,by positivity,?_⟩
  intro g hg k hk
  have hs:Stable g 1:=by unfold Stable;omega
  have hd:[k].sum ≤ dimension g 1:=by simp only[List.sum_singleton,dimension];omega
  have hh:1 ≤ complexity g 1:=by unfold complexity;omega
  have hpos:0 ≤ (g:ℝ):=Nat.cast_nonneg g
  have he:(complexity g 1:ℝ)+1=2*(g:ℝ):=by
    have heN:complexity g 1+1=2*g:=by unfold complexity;omega
    exact_mod_cast heN
  have hsquare:(Real.sqrt (g:ℝ))^2=g:=Real.sq_sqrt hpos
  have hsqH:(Real.sqrt ((complexity g 1:ℝ)+1))^2=(complexity g 1:ℝ)+1:=Real.sq_sqrt (by positivity)
  have hsqrt:Real.sqrt ((complexity g 1:ℝ)+1) ≤ 2*Real.sqrt (g:ℝ):=by
    have h0:=Real.sqrt_nonneg ((complexity g 1:ℝ)+1)
    have h1:=Real.sqrt_nonneg (g:ℝ)
    nlinarith only[hsquare,hsqH,he,hpos,h0,h1]
  have hsqrt':Real.sqrt (complexity g 1:ℝ) ≤ 2*Real.sqrt (g:ℝ):=
    (Real.sqrt_le_sqrt (by linarith)).trans hsqrt
  have hlog: (Real.log ((complexity g 1:ℝ)+1))^2 ≤ 32*Real.sqrt (g:ℝ):=by
    have hx:1 ≤ (complexity g 1:ℝ)+1:=by linarith only[show (0:ℝ) ≤ (complexity g 1:ℝ) from Nat.cast_nonneg _]
    have ht:=Analysis.log_sq_le_sixteen_sqrt _ hx
    nlinarith only[ht,hsqrt]
  have ht:=hb g [k] rfl hs hd 0 ⟨le_rfl,y₀_pos.le⟩
  rw[←mixedJ_div_oneBoundaryModelJ P g k hg hk] at ht
  apply abs_le.mpr
  have hl:=mul_le_mul_of_nonneg_left hlog hC.le
  have hu:=mul_le_mul_of_nonneg_left hsqrt' hC.le
  have hp:0 ≤ C*Real.sqrt (g:ℝ):=mul_nonneg hC.le (Real.sqrt_nonneg _)
  constructor <;>nlinarith only[ht.1,ht.2,hl,hu,hp]

lemma mixedJ_pos_admissible (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    0 < mixedJ P g k:=by
  have hs:Stable g [k].length:=by simp only[List.length_singleton];unfold Stable;omega
  have hd:[k].sum ≤ dimension g [k].length:=by simp only[List.sum_singleton,List.length_singleton,dimension];omega
  have hu:=normalized_pos_valid_nonempty P g [k] (by simp) hs hd 0 ⟨le_rfl,y₀_pos.le⟩
  have hm:=model_pos g [k] 0 hs ⟨le_rfl,y₀_pos.le⟩
  have hratio:0 < ratio P g [k] 0:=div_pos hu hm
  rw[←mixedJ_div_oneBoundaryModelJ P g k hg hk] at hratio
  have hmJ:=oneBoundaryModelJ_pos g k hg
  have ht:=mul_pos hratio hmJ
  rwa[div_mul_cancel₀ _ hmJ.ne'] at ht

lemma logComparisonG_eq_model_errors (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    logComparisonG P g k=
      Real.log (oneBoundaryModelJ g k/(oneBoundaryModelJ g (3*g-2)*(g:ℝ)^(2*(3*g-2-k))))+
      Real.log (mixedJ P g k/oneBoundaryModelJ g k)-
      Real.log (mixedJ P g (3*g-2)/oneBoundaryModelJ g (3*g-2)):=by
  have hJ: mixedJ P g k≠0:=(mixedJ_pos_admissible P g k hg hk).ne'
  have hJN:mixedJ P g (3*g-2)≠0:=(mixedJ_pos_admissible P g (3*g-2) hg le_rfl).ne'
  have hM:oneBoundaryModelJ g k≠0:=(oneBoundaryModelJ_pos g k hg).ne'
  have hMN:oneBoundaryModelJ g (3*g-2)≠0:=(oneBoundaryModelJ_pos g (3*g-2) hg).ne'
  have hg0:(g:ℝ)≠0:=by exact_mod_cast (show g≠0 by omega)
  have hgp:(g:ℝ)^(2*(3*g-2-k))≠0:=pow_ne_zero _ hg0
  unfold logComparisonG
  rw[Real.log_div hJ (mul_ne_zero hJN hgp),Real.log_mul hJN hgp,
    Real.log_div hM (mul_ne_zero hMN hgp),Real.log_mul hMN hgp,
    Real.log_div hJ hM,Real.log_div hJN hMN]
  ring
end WP.Coefficients
