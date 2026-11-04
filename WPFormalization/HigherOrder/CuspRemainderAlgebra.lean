import Mathlib
/-! Finite moment summation of the genuine single-remainder cusp bound.
This generic real algebra is used with actual b moments in CuspRemainderStep. -/
noncomputable section
namespace WP.HigherOrder
lemma weighted_cusp_remainder_algebra (b f:ℕ→ℝ) (err A E F S h Cm:ℝ) (e:ℕ→ℝ) (L:ℕ)
    (hA:0 ≤ A) (hE:0 ≤ E) (hF:0 ≤ F) (hS:0<S) (hh:0<h) (hCm:0 ≤ Cm)
    (he:∀i:ℕ,0 ≤ e i) (hactual:HasSum f err)
    (hmom:∀i:ℕ,i ≤ L→Summable (fun d:ℕ=>|b d| *((S+(d:ℝ)+1)^(2*i))) ∧
      (∑'d:ℕ,|b d| *((S+(d:ℝ)+1)^(2*i))) ≤ Cm*S^(2*i))
    (hpoint:∀d:ℕ,|f d| ≤ A*((E/h^L)*(|b d| *(S+(d:ℝ)+1)^(2*L))+
      (F*S^(2*L)/h^L)*(∑i∈Finset.range L,
        (e i/(S^(2*i)*((L-i).factorial:ℝ)))*(|b d| *(S+(d:ℝ)+1)^(2*i))))) :
    |err| ≤ A*Cm*S^(2*L)/h^L*(E+F*(∑i∈Finset.range L,e i/((L-i).factorial:ℝ))) :=by
  let w:ℕ→ℕ→ℝ:=fun i d=>|b d| *(S+(d:ℝ)+1)^(2*i)
  let k:ℕ→ℝ:=fun i=>e i/(S^(2*i)*((L-i).factorial:ℝ))
  have hwi (i:ℕ) (hi:i ≤ L):HasSum (w i) (∑'d:ℕ,w i d):=(hmom i hi).1.hasSum
  have hW (i:ℕ) (hi:i ≤ L):(∑'d:ℕ,w i d) ≤ Cm*S^(2*i):=(hmom i hi).2
  have hk (i:ℕ):0 ≤ k i:=by
    have hei:=he i
    dsimp[k]
    positivity
  have hknown:HasSum (fun d:ℕ=>∑i∈Finset.range L,k i*w i d)
      (∑i∈Finset.range L,k i*(∑'d:ℕ,w i d)):=by
    apply hasSum_sum
    intro i hi
    exact (hwi i (Finset.mem_range.mp hi).le).mul_left (k i)
  have hmajor:=(((hwi L le_rfl).mul_left (E/h^L)).add
    (hknown.mul_left (F*S^(2*L)/h^L))).mul_left A
  have hsumNorm:Summable (fun d:ℕ=>|f d|):=by simpa only[Real.norm_eq_abs] using hactual.summable.norm
  have hle:|err| ≤ A*((E/h^L)*(∑'d:ℕ,w L d)+
      (F*S^(2*L)/h^L)*(∑i∈Finset.range L,k i*(∑'d:ℕ,w i d))):=by
    have hn:=norm_tsum_le_tsum_norm hactual.summable.norm
    rw[hactual.tsum_eq] at hn
    simp only[Real.norm_eq_abs] at hn
    apply hn.trans
    have hh':=hsumNorm.tsum_le_tsum hpoint hmajor.summable
    exact hh'.trans_eq hmajor.tsum_eq
  have hfirst:(E/h^L)*(∑'d:ℕ,w L d) ≤ (E/h^L)*(Cm*S^(2*L)):=
    mul_le_mul_of_nonneg_left (hW L le_rfl) (by positivity)
  have hsecond:(∑i∈Finset.range L,k i*(∑'d:ℕ,w i d)) ≤
      Cm*(∑i∈Finset.range L,e i/((L-i).factorial:ℝ)):=by
    rw[Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply (mul_le_mul_of_nonneg_left (hW i (Finset.mem_range.mp hi).le) (hk i)).trans_eq
    dsimp[k]
    field_simp[show S≠0 from hS.ne',show ((L-i).factorial:ℝ)≠0 by positivity]
    <;>ring
  apply hle.trans
  apply (mul_le_mul_of_nonneg_left (add_le_add hfirst
    (mul_le_mul_of_nonneg_left hsecond (by positivity))) hA).trans_eq
  ring
end WP.HigherOrder
