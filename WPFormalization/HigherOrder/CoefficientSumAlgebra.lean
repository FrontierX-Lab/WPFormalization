import WPFormalization.HigherOrder.Triangular
import WPFormalization.HigherOrder.FiniteRemainderAlgebra
/-! Genuine coefficientwise sum algebra with the required summability.
Finite truncations commute with a weighted sum once each of the finitely
many coefficient sums is actually summable. The resulting operator
remainder is an exact HasSum, not an assumed error recurrence. -/
noncomputable section
namespace WP.HigherOrder
lemma coefficientSum_mul_left (a:Series) (f:ℕ→Series)
    (hf:∀n:ℕ,Summable (fun l:ℕ=>PowerSeries.coeff n (f l))) :
    coefficientSum (fun l=>a*f l)=a*coefficientSum f:=by
  apply PowerSeries.ext
  intro n
  simp only[coefficientSum_coeff,PowerSeries.coeff_mul]
  have hh:=hasSum_sum (s:=(Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ×ℕ))) (fun ij hij=>(hf ij.2).hasSum.mul_left (PowerSeries.coeff ij.1 a))
  simpa only[coefficientSum_coeff] using hh.tsum_eq

lemma coefficientSum_mul_left_hasSum (a:Series) (f:ℕ→Series)
    (hf:∀n:ℕ,Summable (fun l:ℕ=>PowerSeries.coeff n (f l))) (n:ℕ) :
    HasSum (fun l:ℕ=>PowerSeries.coeff n (a*f l))
      (PowerSeries.coeff n (a*coefficientSum f)):=by
  simp only[PowerSeries.coeff_mul,coefficientSum_coeff]
  exact hasSum_sum (s:=(Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ×ℕ)))
    (fun ij hij=>(hf ij.2).hasSum.mul_left (PowerSeries.coeff ij.1 a))

lemma coefficientSum_C_mul (c:ℝ) (f:ℕ→Series) :
    coefficientSum (fun l=>PowerSeries.C c*f l)=PowerSeries.C c*coefficientSum f:=by
  apply PowerSeries.ext
  intro n
  simp only[coefficientSum_coeff,PowerSeries.coeff_C_mul,tsum_mul_left]

lemma weighted_truncation_hasSum (a:ℕ→ℝ) (f:ℕ→Series) (L:ℕ) (t:ℝ)
    (hf:∀n:ℕ,n<L→Summable (fun l:ℕ=>a l*PowerSeries.coeff n (f l))) :
    HasSum (fun l:ℕ=>a l*truncationValue (f l) L t)
      (truncationValue (coefficientSum (fun l=>PowerSeries.C (a l)*f l)) L t):=by
  have hs (n:ℕ) (hn:n∈Finset.range L):HasSum (fun l:ℕ=>(a l*PowerSeries.coeff n (f l))*t^n)
      ((∑'l:ℕ,a l*PowerSeries.coeff n (f l))*t^n):=
    (hf n (Finset.mem_range.mp hn)).hasSum.mul_right (t^n)
  have hh:=hasSum_sum (s:=Finset.range L) hs
  convert hh using 1
  · funext l
    simp only[truncationValue,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp only[truncationValue,coefficientSum_coeff,PowerSeries.coeff_C_mul]

lemma weighted_operator_remainder_hasSum (a v:ℕ→ℝ) (f:ℕ→Series) (L:ℕ) (t value:ℝ)
    (hv:HasSum (fun l=>a l*v l) value)
    (hf:∀n:ℕ,n<L→Summable (fun l:ℕ=>a l*PowerSeries.coeff n (f l))) :
    HasSum (fun l=>a l*(v l-truncationValue (f l) L t))
      (value-truncationValue (coefficientSum (fun l=>PowerSeries.C (a l)*f l)) L t):=by
  convert hv.sub (weighted_truncation_hasSum a f L t hf) using 1
  funext l
  ring
end WP.HigherOrder
