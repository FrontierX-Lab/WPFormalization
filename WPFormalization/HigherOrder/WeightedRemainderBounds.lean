import Mathlib
/-! Actual weighted HasSum remainders inherit a polynomial kernel moment
bound. Summability and the actual sum value are retained explicitly. -/
noncomputable section
namespace WP.HigherOrder
lemma weighted_actual_remainder_bound (a r:ℕ→ℝ) (err S B C:ℝ) (k:ℕ)
    (hB:0 ≤ B) (hactual:HasSum (fun l=>a l*r l) err)
    (hs:Summable (fun l:ℕ=>(S+l+1)^k*|a l|))
    (hm:(∑'l:ℕ,(S+l+1)^k*|a l|) ≤ C*S^k)
    (hr:∀l:ℕ,|r l| ≤ B*(S+l+1)^k) : |err| ≤ C*B*S^k:=by
  have hpoint (l:ℕ):|a l*r l| ≤ B*((S+l+1)^k*|a l|):=by
    rw[abs_mul]
    convert mul_le_mul_of_nonneg_left (hr l) (abs_nonneg (a l)) using 1 <;>ring
  have hn:Summable (fun l:ℕ=>|a l*r l|):=by simpa only[Real.norm_eq_abs] using hactual.summable.norm
  have hnorm:=norm_tsum_le_tsum_norm hactual.summable.norm
  rw[hactual.tsum_eq] at hnorm
  simp only[Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  calc
    _ ≤ ∑'l:ℕ,B*((S+l+1)^k*|a l|):=hn.tsum_le_tsum hpoint (hs.mul_left B)
    _=B*(∑'l:ℕ,(S+l+1)^k*|a l|):=tsum_mul_left
    _ ≤ B*(C*S^k):=mul_le_mul_of_nonneg_left hm hB
    _=_:=by ring
end WP.HigherOrder
