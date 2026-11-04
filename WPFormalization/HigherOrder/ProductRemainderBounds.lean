import WPFormalization.HigherOrder.FiniteRemainderAlgebra
/-! The normalized finite product remainder with one unknown error per
term. It records the known-coefficient convolution needed in C.3. -/
noncomputable section
namespace WP.HigherOrder
lemma product_remainder_scaled_bound (x y:ℝ) (f g:PowerSeries ℝ) (q:ℕ) (hq:1 ≤ q)
    (S n Cq:ℝ) (e E:ℕ→ℝ) (hS:0 ≤ S) (hn:0<n) (hCq:0 ≤ Cq)
    (he:∀i:ℕ,0 ≤ e i) (hE:∀i:ℕ,0 ≤ E i) (hy:|y| ≤ 1)
    (hx:|x-truncationValue f q (1/n)| ≤ Cq*S^(2*q)/n^q)
    (hf:∀i:ℕ,i<q→|PowerSeries.coeff i f| ≤ e i*S^(2*i))
    (hg:∀j:ℕ,1 ≤ j→j ≤ q→|y-truncationValue g j (1/n)| ≤ E j*S^(2*j)/n^j) :
    |x*y-truncationValue (f*g) q (1/n)| ≤
      (S^(2*q)/n^q)*(Cq+∑i∈Finset.range q,e i*E (q-i)) :=by
  have hnorm:=exact_product_remainder_norm_le x y f g q (1/n)
  simp only[Real.norm_eq_abs] at hnorm
  have hfirst:|x-truncationValue f q (1/n)| *|y| ≤ Cq*S^(2*q)/n^q:=by
    have hb:=mul_le_mul hx hy (abs_nonneg _) (by positivity:0 ≤ Cq*S^(2*q)/n^q)
    simpa only[mul_one] using hb
  have hterm (i:ℕ) (hi:i∈Finset.range q):
      |PowerSeries.coeff i f| *|1/n|^i*|y-truncationValue g (q-i) (1/n)| ≤
        (S^(2*q)/n^q)*(e i*E (q-i)):=by
    have hiq:i<q:=Finset.mem_range.mp hi
    have hei:=he i
    have hEi:=hE (q-i)
    have hcoef:|PowerSeries.coeff i f| *|1/n|^i ≤ e i*S^(2*i)/n^i:=by
      rw[abs_of_pos (one_div_pos.mpr hn)]
      convert mul_le_mul_of_nonneg_right (hf i hiq) (pow_nonneg (one_div_pos.mpr hn).le i) using 1 <;>
        rw[div_pow,one_pow]<;>ring
    have hg':=hg (q-i) (by omega) (by omega)
    apply (mul_le_mul hcoef hg' (abs_nonneg _) (by positivity:0 ≤ e i*S^(2*i)/n^i)).trans_eq
    have hSp:S^(2*i)*S^(2*(q-i))=S^(2*q):=by rw[←pow_add];congr 1;omega
    have hnp:n^i*n^(q-i)=n^q:=by rw[←pow_add,Nat.add_sub_of_le hiq.le]
    calc
      _=e i*E (q-i)*(S^(2*i)*S^(2*(q-i)))/(n^i*n^(q-i)):=by ring
      _=_:=by rw[hSp,hnp];ring
  apply hnorm.trans
  apply (add_le_add hfirst (Finset.sum_le_sum hterm)).trans_eq
  rw[←Finset.mul_sum]
  ring
end WP.HigherOrder
