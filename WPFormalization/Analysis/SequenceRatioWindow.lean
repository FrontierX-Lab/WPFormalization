import Mathlib
/-! Finite telescoping and short-window ratios for a positive adjacent sequence. -/
set_option autoImplicit false
noncomputable section
namespace WP.Analysis

lemma sequence_total_drop_le (u:ℕ→ℝ)(d:ℝ)(N:ℕ)(hu:u 0=1)
    (hd:∀j:ℕ,j < N →u j-u (j+1) ≤ d*((j:ℝ)+1)):
    ∀k:ℕ,k ≤ N →1-u k ≤ d*(k:ℝ)*((k:ℝ)+1)/2:=by
  intro k
  induction k with
  | zero=>intro _;simp[hu]
  | succ k ih=>
    intro hk
    have hi:=ih (by omega)
    have hs:=hd k (by omega)
    push_cast
    nlinarith only[hi,hs]

lemma sequence_adjacent_ratio_short_window (u:ℕ→ℝ)(d:ℝ)(N k:ℕ)(hu:u 0=1)
    (hd:∀j:ℕ,j < N →0 ≤ u j-u (j+1) ∧ u j-u (j+1) ≤ d*((j:ℝ)+1))
    (hk:k < N)(hw:d*((k:ℝ)+1)*((k:ℝ)+2) ≤ 1):
    0 ≤ u k/u (k+1)-1 ∧ u k/u (k+1)-1 ≤ 2*d*((k:ℝ)+1):=by
  have hdrop:=sequence_total_drop_le u d N hu (fun j hj=>(hd j hj).2) (k+1) (by omega)
  have hden:(1/2:ℝ) ≤ u (k+1):=by
    push_cast at hdrop
    nlinarith only[hdrop,hw]
  have hp:0 < u (k+1):=lt_of_lt_of_le (by norm_num) hden
  have hδ:0 ≤ d*((k:ℝ)+1):=(hd k hk).1.trans (hd k hk).2
  have he:u k/u (k+1)-1=(u k-u (k+1))/u (k+1):=by field_simp <;>ring
  rw[he]
  refine ⟨div_nonneg (hd k hk).1 hp.le,?_⟩
  apply (div_le_iff₀ hp).mpr
  have hm:=mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num:(0:ℝ) ≤ 2) hδ)
  nlinarith only[(hd k hk).2,hm]
end WP.Analysis
