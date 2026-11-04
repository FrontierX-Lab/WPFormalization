import Mathlib
/-! Lower logarithmic cost of a finite block of adjacent ratio gaps, from the actual telescoping sum. -/
set_option autoImplicit false
noncomputable section
namespace WP.Analysis

lemma quarter_le_log_one_add_half {r:ℝ}(hr:0 ≤ r)(hr1:r ≤ 1):
    r/4 ≤ Real.log (1+r/2):=by
  have H:=Real.one_sub_inv_le_log_of_pos (by positivity:0 < 1+r/2)
  have he:r/4 ≤ 1-(1+r/2)⁻¹:=by
    have hden:0 < 1+r/2:=by positivity
    apply (le_sub_iff_add_le).mpr
    apply (le_sub_iff_add_le').mp
    change (1+r/2)⁻¹ ≤ 1-r/4
    rw[inv_eq_one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith only[hr,hr1,mul_le_mul_of_nonneg_left hr1 hr]
  exact he.trans H

lemma sum_log_adjacent_telescope (u:ℕ→ℝ)(a L:ℕ)
    (hu:∀j:ℕ,j ≤ L →0 < u (a+j)):
    ∑i∈Finset.range L,Real.log (u (a+i)/u (a+i+1))=
      Real.log (u a)-Real.log (u (a+L)):=by
  induction L with
  | zero=>simp
  | succ L ih=>
    rw[Finset.sum_range_succ,ih (fun j hj=>hu j (by omega))]
    rw[Real.log_div (hu L (by omega)).ne' (by simpa only[Nat.add_assoc] using (hu (L+1) le_rfl).ne')]
    simp only[Nat.add_succ]
    ring

lemma finite_log_ratio_block_bound (u:ℕ→ℝ)(k L:ℕ)(r:ℝ)
    (hr:0 ≤ r)(hr1:r ≤ 1)(hu:∀j:ℕ,j ≤ L →0 < u (k+j))
    (hzero:0 < u 0)(hstart:u k ≤ u 0)
    (hgap:∀i:ℕ,i < L →1+r/2 ≤ u (k+i)/u (k+i+1)):
    r*(L:ℝ)/4 ≤ Real.log (u 0/u (k+L)):=by
  have ht:=sum_log_adjacent_telescope u k L hu
  have hbound:r*(L:ℝ)/4 ≤ ∑i∈Finset.range L,Real.log (u (k+i)/u (k+i+1)):=by
    calc
      _ = ∑i∈Finset.range L,r/4:=by simp;ring
      _ ≤ _:=by
        apply Finset.sum_le_sum
        intro i hi
        apply (quarter_le_log_one_add_half hr hr1).trans
        exact Real.log_le_log (by positivity) (hgap i (Finset.mem_range.mp hi))
  rw[ht] at hbound
  rw[Real.log_div hzero.ne' (hu L le_rfl).ne']
  have hk:0 < u k:=by simpa only[Nat.add_zero] using hu 0 (by omega)
  have hlog:Real.log (u k) ≤ Real.log (u 0):=Real.log_le_log hk hstart
  linarith only[hbound,hlog]
end WP.Analysis
