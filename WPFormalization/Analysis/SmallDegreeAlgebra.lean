import Mathlib
/-! Elementary rate extraction from a short-window estimate and a truncated squared-gap bound. All sequence hypotheses are proved for the actual brackets by the consuming module. -/
set_option autoImplicit false
noncomputable section
namespace WP.Analysis
lemma small_degree_truncated_gap_rate (A D:ℝ)(hA:0 < A)(hD:0 < D):
    ∃E T:ℝ,0 < E∧1 ≤ T∧∀x q L t η:ℝ,T ≤ t →0 < q →q ≤ t^6+1 →
      x=t^8 →0 ≤ L →L ≤ 16*t →0 ≤ η →
      (A*q^2 ≤ x →η ≤ A*q/x) →
      (min η 1)^2*q ≤ D*L^2+D*q^2/x →η ≤ E/t:=by
  let S:ℝ:=Real.sqrt (256*D*Real.sqrt A+2*D)
  have hS:0 ≤ S:=Real.sqrt_nonneg _
  have hS2:S^2=256*D*Real.sqrt A+2*D:=Real.sq_sqrt (by positivity)
  let E:ℝ:=2*A+S+1
  let T:ℝ:=E+1
  have hE:0 < E:=by dsimp[E];positivity
  have hT:1 ≤ T:=by dsimp[T];linarith only[hE]
  refine ⟨E,T,hE,hT,?_⟩
  intro x q L t η ht hq hqt hx hL hLt hη hshort hgap
  have ht1:1 ≤ t:=hT.trans ht
  have ht0:0 < t:=zero_lt_one.trans_le ht1
  have hx0:0 < x:=by rw[hx];positivity
  have ht6:1 ≤ t^6:=one_le_pow₀ ht1
  have hqU:q ≤ 2*t^6:=by linarith only[hqt,ht6]
  have hE2:2*A ≤ E:=by dsimp[E];linarith only[hS]
  have hES:S ≤ E:=by dsimp[E];linarith only[hA]
  by_cases hw:A*q^2 ≤ x
  · have hηb:=hshort hw
    have hqscale:q/x ≤ 2/t^2:=by
      apply (div_le_div_iff₀ hx0 (by positivity:0 < t^2)).mpr
      have H:=mul_le_mul_of_nonneg_right hqU (show (0:ℝ) ≤ t^2 by positivity)
      rw[hx]
      nlinarith only[H]
    have hη2:η ≤ 2*A/t^2:=by
      have H:=mul_le_mul_of_nonneg_left hqscale hA.le
      simp only[div_eq_mul_inv] at hηb H ⊢
      nlinarith only[hηb,H]
    calc
      _ ≤ 2*A/t^2:=hη2
      _ ≤ 2*A/t:=div_le_div_of_nonneg_left (by positivity) ht0 (by nlinarith only[ht1])
      _ ≤ E/t:=div_le_div_of_nonneg_right hE2 ht0.le
  · have hAsq:(Real.sqrt A)^2=A:=Real.sq_sqrt hA.le
    have hqlo:t^4 ≤ Real.sqrt A*q:=by
      apply (sq_le_sq₀ (by positivity:0 ≤ t^4) (by positivity:0 ≤ Real.sqrt A*q)).mp
      calc
        _ = x:=by rw[hx];ring
        _ ≤ A*q^2:=(le_of_not_ge hw)
        _ = (Real.sqrt A)^2*q^2:=congrArg (fun z:ℝ=>z*q^2) hAsq.symm
        _ = _:=by ring
    have hfirst:t^2/q ≤ Real.sqrt A/t^2:=by
      apply (div_le_div_iff₀ hq (by positivity:0 < t^2)).mpr
      nlinarith only[hqlo]
    have hsecond:q/x ≤ 2/t^2:=by
      apply (div_le_div_iff₀ hx0 (by positivity:0 < t^2)).mpr
      have H:=mul_le_mul_of_nonneg_right hqU (show (0:ℝ) ≤ t^2 by positivity)
      rw[hx]
      nlinarith only[H]
    have hsq:L^2 ≤ 256*t^2:=by nlinarith only[hL,hLt]
    have hgap':(min η 1)^2 ≤ (D*L^2+D*q^2/x)/q:=(le_div_iff₀ hq).mpr hgap
    have hnorm:(D*L^2+D*q^2/x)/q=D*L^2/q+D*q/x:=by field_simp <;>ring
    rw[hnorm] at hgap'
    have H1:=mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq hq.le) hD.le
    have H2:=mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 256*D by positivity)
    have H3:=mul_le_mul_of_nonneg_left hsecond hD.le
    have hminsq:(min η 1)^2 ≤ S^2/t^2:=by
      rw[hS2]
      simp only[div_eq_mul_inv] at hgap' H1 H2 H3 ⊢
      nlinarith only[hgap',H1,H2,H3]
    have hmin0:0 ≤ min η 1:=le_min hη (by norm_num)
    have hmin:min η 1 ≤ S/t:=by
      apply (sq_le_sq₀ hmin0 (by positivity:0 ≤ S/t)).mp
      simpa only[div_pow] using hminsq
    have hST:S < t:=by dsimp[T,E] at ht;linarith only[ht,hA]
    have hSt:S/t < 1:=(div_lt_one ht0).mpr hST
    have hη1:η ≤ 1:=by
      by_contra H
      rw[min_eq_right (le_of_not_ge H)] at hmin
      linarith only[hmin,hSt]
    rw[min_eq_left hη1] at hmin
    exact hmin.trans (div_le_div_of_nonneg_right hES ht0.le)
end WP.Analysis
