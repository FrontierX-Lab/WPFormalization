import Mathlib
/-! The finite product and reciprocal identities used in Appendix C.3.
Each recursive product step has one exact remainder; no products of unknown
remainders are introduced. The inverse identity retains its actual negative
sign, and the norm estimates only use the exact displayed identities. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

def truncationValue {R:Type*} [CommSemiring R] (f:PowerSeries R) (q:ℕ) (t:R) : R :=
  ∑j∈Finset.range q,PowerSeries.coeff j f*t^j

lemma truncationValue_mul {R:Type*} [CommSemiring R] (f g:PowerSeries R) (q:ℕ) (t:R) :
    truncationValue (f*g) q t=
      ∑i∈Finset.range q,PowerSeries.coeff i f*t^i*truncationValue g (q-i) t := by
  calc
    _=∑k∈Finset.range q,∑i∈Finset.range (k+1),
        PowerSeries.coeff i f*PowerSeries.coeff (k-i) g*t^(i+(k-i)):=by
      simp only[truncationValue,PowerSeries.coeff_mul,Finset.sum_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      rw[show i+(k-i)=k by have hh:=Finset.mem_range.mp hi;omega]
    _=∑i∈Finset.range q,∑j∈Finset.range (q-i),
        PowerSeries.coeff i f*PowerSeries.coeff j g*t^(i+j):=
      Finset.sum_range_diag_flip q (fun i j=>PowerSeries.coeff i f*PowerSeries.coeff j g*t^(i+j))
    _=_:=by
      simp only[truncationValue,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw[pow_add]
      ring

lemma truncationValue_one {R:Type*} [CommSemiring R] (q:ℕ) (hq:1 ≤ q) (t:R) :
    truncationValue (1:PowerSeries R) q t=1 := by
  have hq0:0<q:=by omega
  simp[truncationValue,PowerSeries.coeff_one,hq0]

lemma exact_product_remainder_identity {R:Type*} [CommRing R]
    (x y:R) (f g:PowerSeries R) (q:ℕ) (t:R) :
    x*y-truncationValue (f*g) q t=
      (x-truncationValue f q t)*y+
        ∑j∈Finset.range q,PowerSeries.coeff j f*t^j*(y-truncationValue g (q-j) t) := by
  rw[truncationValue_mul]
  simp only[mul_sub,Finset.sum_sub_distrib]
  have hs:(∑j∈Finset.range q,PowerSeries.coeff j f*t^j*y)=truncationValue f q t*y:=by
    rw[truncationValue,Finset.sum_mul]
  rw[hs]
  ring

lemma exact_inverse_defect_identity {R:Type*} [CommRing R] (x:R) (f d:PowerSeries R)
    (hfd:f*d=1) (q:ℕ) (hq:1 ≤ q) (t:R) :
    x*truncationValue d q t-1=
      ∑j∈Finset.range q,PowerSeries.coeff j d*t^j*(x-truncationValue f (q-j) t) := by
  have hdf:d*f=1:=by rw[mul_comm,hfd]
  have hprod:=truncationValue_mul d f q t
  rw[hdf,truncationValue_one q hq t] at hprod
  simp only[mul_sub,Finset.sum_sub_distrib]
  rw[←hprod]
  have hs:(∑j∈Finset.range q,PowerSeries.coeff j d*t^j*x)=truncationValue d q t*x:=by
    rw[truncationValue,Finset.sum_mul]
  rw[hs]
  ring

lemma exact_inverse_remainder_identity {R:Type*} [Field R] (x:R) (hx:x≠0) (f d:PowerSeries R)
    (hfd:f*d=1) (q:ℕ) (hq:1 ≤ q) (t:R) :
    x⁻¹-truncationValue d q t=
      -x⁻¹*∑j∈Finset.range q,PowerSeries.coeff j d*t^j*(x-truncationValue f (q-j) t) := by
  rw[←exact_inverse_defect_identity x f d hfd q hq t]
  field_simp
  ring
lemma exact_product_remainder_norm_le {R:Type*} [NormedCommRing R] [NormOneClass R]
    (x y:R) (f g:PowerSeries R) (q:ℕ) (t:R) :
    ‖x*y-truncationValue (f*g) q t‖ ≤
      ‖x-truncationValue f q t‖*‖y‖+
        ∑j∈Finset.range q,‖PowerSeries.coeff j f‖*‖t‖^j*‖y-truncationValue g (q-j) t‖ := by
  rw[exact_product_remainder_identity]
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_mul_le _ _) ((norm_sum_le _ _).trans _)
  apply Finset.sum_le_sum
  intro j hj
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le _ _) (norm_nonneg _))) (norm_nonneg _))

lemma exact_inverse_remainder_norm_le {R:Type*} [NormedField R] (x:R) (hx:x≠0)
    (f d:PowerSeries R) (hfd:f*d=1) (q:ℕ) (hq:1 ≤ q) (t:R) :
    ‖x⁻¹-truncationValue d q t‖ ≤
      ‖x⁻¹‖*∑j∈Finset.range q,‖PowerSeries.coeff j d‖*‖t‖^j*‖x-truncationValue f (q-j) t‖ := by
  rw[exact_inverse_remainder_identity x hx f d hfd q hq t]
  calc
    _ ≤ ‖-x⁻¹‖*‖∑j∈Finset.range q,PowerSeries.coeff j d*t^j*(x-truncationValue f (q-j) t)‖ :=norm_mul_le _ _
    _ ≤ ‖x⁻¹‖*∑j∈Finset.range q,‖PowerSeries.coeff j d‖*‖t‖^j*‖x-truncationValue f (q-j) t‖ :=by
      rw[norm_neg]
      apply mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans _) (norm_nonneg _)
      apply Finset.sum_le_sum
      intro j hj
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le _ _) (norm_nonneg _))) (norm_nonneg _))
end WP.HigherOrder
