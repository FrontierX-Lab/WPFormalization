import WPFormalization.HigherOrder.FiniteRemainderAlgebra
import WPFormalization.HigherOrder.ProductRemainderBounds
import WPFormalization.HigherOrder.SmallWeightRegion
/-! Normalized finite scalar product and inverse errors. Each summand has
one actual remainder multiplied by known formal coefficients; no product of
unknown errors is introduced. These are numeric supporting steps, whose
actual C.3 clients must supply the stated local induction data. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder

lemma product_remainder_scaled_bound_uniform (x y:ℝ)(f g:PowerSeries ℝ)(q:ℕ)(hq:1≤q)
    (S h X Cq:ℝ)(e E:ℕ→ℝ)(hS:0≤S)(hh:0<h)(hX:0≤X)(hCq:0≤Cq)
    (he:∀i,0≤e i)(hE:∀i,0≤E i)(hy:|y|≤X)
    (hx:|x-truncationValue f q (1/h)|≤Cq*S^(2*q)/h^q)
    (hf:∀i<q,|PowerSeries.coeff i f|≤e i*S^(2*i))
    (hg:∀k:ℕ,1≤k→k≤q→|y-truncationValue g k (1/h)|≤E k*S^(2*k)/h^k):
    |x*y-truncationValue (f*g) q (1/h)|≤
      (S^(2*q)/h^q)*(Cq*X+∑i∈Finset.range q,e i*E (q-i)):=by
  have hn:=exact_product_remainder_norm_le x y f g q (1/h)
  simp only[Real.norm_eq_abs] at hn
  have hfirst:|x-truncationValue f q (1/h)| *|y|≤(S^(2*q)/h^q)*(Cq*X):=by
    have hb:=mul_le_mul hx hy (abs_nonneg _) (by positivity:0≤Cq*S^(2*q)/h^q)
    convert hb using 1 <;> ring
  have hterm(i:ℕ)(hi:i∈Finset.range q):
      |PowerSeries.coeff i f| *|1/h|^i*|y-truncationValue g (q-i) (1/h)|≤
        (S^(2*q)/h^q)*(e i*E (q-i)):=by
    have hiq:i<q:=Finset.mem_range.mp hi
    have hei:0≤e i:=he i
    have hEi:0≤E (q-i):=hE (q-i)
    have hcoef:|PowerSeries.coeff i f| *|1/h|^i≤e i*S^(2*i)/h^i:=by
      rw[abs_of_pos (one_div_pos.mpr hh)]
      convert mul_le_mul_of_nonneg_right (hf i hiq) (pow_nonneg (one_div_pos.mpr hh).le i) using 1 <;>
        rw[div_pow,one_pow] <;> ring
    have hg':=hg (q-i) (by omega) (by omega)
    apply (mul_le_mul hcoef hg' (abs_nonneg _) (by positivity:0≤e i*S^(2*i)/h^i)).trans_eq
    have hSp:S^(2*i)*S^(2*(q-i))=S^(2*q):=by rw[←pow_add];congr 1;omega
    have hhp:h^i*h^(q-i)=h^q:=by rw[←pow_add,Nat.add_sub_of_le hiq.le]
    calc
      _=e i*E (q-i)*(S^(2*i)*S^(2*(q-i)))/(h^i*h^(q-i)):=by ring
      _=_:=by rw[hSp,hhp];ring
  apply hn.trans
  apply (add_le_add hfirst (Finset.sum_le_sum hterm)).trans_eq
  rw[←Finset.mul_sum]
  ring

lemma inverse_remainder_scaled_bound (x:ℝ)(f d:PowerSeries ℝ)(hfd:f*d=1)(hc:1/2≤x)
    (q:ℕ)(hq:1≤q)(S h:ℝ)(e E:ℕ→ℝ)(hS:0≤S)(hh:0<h)
    (he:∀i,0≤e i)(hE:∀i,0≤E i)
    (hd:∀i<q,|PowerSeries.coeff i d|≤e i*S^(2*i))
    (hf:∀k:ℕ,1≤k→k≤q→|x-truncationValue f k (1/h)|≤E k*S^(2*k)/h^k):
    |x⁻¹-truncationValue d q (1/h)|≤
      (S^(2*q)/h^q)*(2*∑i∈Finset.range q,e i*E (q-i)):=by
  have hxp:0<x:=by linarith
  have hinv:|x⁻¹|≤2:=by
    rw[abs_inv,abs_of_pos hxp,←one_div]
    apply (div_le_iff₀ hxp).mpr
    linarith
  have hn:=exact_inverse_remainder_norm_le x hxp.ne' f d hfd q hq (1/h)
  simp only[Real.norm_eq_abs] at hn
  have hterm(i:ℕ)(hi:i∈Finset.range q):
      |PowerSeries.coeff i d| *|1/h|^i*|x-truncationValue f (q-i) (1/h)|≤
        (S^(2*q)/h^q)*(e i*E (q-i)):=by
    have hiq:i<q:=Finset.mem_range.mp hi
    have hei:0≤e i:=he i
    have hEi:0≤E (q-i):=hE (q-i)
    have hcoef:|PowerSeries.coeff i d| *|1/h|^i≤e i*S^(2*i)/h^i:=by
      rw[abs_of_pos (one_div_pos.mpr hh)]
      convert mul_le_mul_of_nonneg_right (hd i hiq) (pow_nonneg (one_div_pos.mpr hh).le i) using 1 <;>
        rw[div_pow,one_pow] <;> ring
    have hf':=hf (q-i) (by omega) (by omega)
    apply (mul_le_mul hcoef hf' (abs_nonneg _) (by positivity:0≤e i*S^(2*i)/h^i)).trans_eq
    have hSp:S^(2*i)*S^(2*(q-i))=S^(2*q):=by rw[←pow_add];congr 1;omega
    have hhp:h^i*h^(q-i)=h^q:=by rw[←pow_add,Nat.add_sub_of_le hiq.le]
    calc
      _=e i*E (q-i)*(S^(2*i)*S^(2*(q-i)))/(h^i*h^(q-i)):=by ring
      _=_:=by rw[hSp,hhp];ring
  apply hn.trans
  have hs:=Finset.sum_le_sum hterm
  have hs0:0≤∑i∈Finset.range q,e i*E (q-i):=Finset.sum_nonneg (fun i hi=>mul_nonneg (he i) (hE (q-i)))
  calc
    _ ≤ 2*∑i∈Finset.range q,(S^(2*q)/h^q)*(e i*E (q-i)):=
      mul_le_mul hinv hs (Finset.sum_nonneg (fun i hi=>by positivity)) (by norm_num)
    _ = _:=by rw[←Finset.mul_sum];ring
end WP.HigherOrder
