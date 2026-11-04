import WPFormalization.HigherOrder.ShiftRemainder
/-! Exact X-prefactor extraction and actual linear atom remainder algebra.
A zero formal constant removes any current-order scalar error from the
known-prefix sum. These are finite identities and norm bounds only. -/
noncomputable section
namespace WP.HigherOrder
lemma truncationValue_C_mul (a:ℝ) (f:Series) (L:ℕ) (t:ℝ) :
    truncationValue (PowerSeries.C a*f) L t=a*truncationValue f L t:=by
  simp only[truncationValue,PowerSeries.coeff_C_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma truncationValue_X_mul (f:Series) (L:ℕ) (hL:1 ≤ L) (t:ℝ) :
    truncationValue (PowerSeries.X*f) L t=t*truncationValue f (L-1) t:=by
  cases L with
  | zero=>omega
  | succ q=>
    simp only[Nat.add_sub_cancel,truncationValue]
    rw[Finset.sum_range_succ']
    have hzero:PowerSeries.coeff 0 (PowerSeries.X*f)=0:=by
      simp only[PowerSeries.coeff_zero_eq_constantCoeff,map_mul,PowerSeries.constantCoeff_X,zero_mul]
    rw[hzero,zero_mul,add_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hcoef:=PowerSeries.coeff_X_pow_mul f 1 i
    simp only[pow_one] at hcoef
    rw[hcoef,pow_succ]
    ring

lemma complexityShift_mul (c:ℝ) (f g:Series) :
    complexityShift c (f*g)=complexityShift c f*complexityShift c g:=by
  exact PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' (shiftVariable_constant c)) f g

lemma complexityShift_X (c:ℝ) :complexityShift c PowerSeries.X=shiftVariable c:=by
  exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' (shiftVariable_constant c))

lemma shifted_loss_one_formal_identity (a c:ℝ) (f g:Series) :
    PowerSeries.C a*complexityShift c (PowerSeries.X*(f*g))=
      PowerSeries.C a*shiftVariable c*complexityShift c f*complexityShift c g:=by
  rw[complexityShift_mul,complexityShift_mul,complexityShift_X]
  ring

lemma exact_loss_one_remainder_identity (x y a c h:ℝ) (f g:Series) (L:ℕ) (hL:1 ≤ L) :
    a/(h-c)*(x*y)-truncationValue (PowerSeries.C a*complexityShift c (PowerSeries.X*(f*g))) L (1/h)=
      a/(h-c)*(x*y-truncationValue (f*g) (L-1) (1/(h-c)))+
      a*(truncationValue (PowerSeries.X*(f*g)) L (1/(h-c))-
        truncationValue (complexityShift c (PowerSeries.X*(f*g))) L (1/h)):=by
  rw[truncationValue_C_mul,truncationValue_X_mul _ _ hL]
  ring

lemma loss_one_remainder_bound (x y a c h:ℝ) (f g:Series) (L:ℕ) (hL:1 ≤ L) :
    |a/(h-c)*(x*y)-truncationValue (PowerSeries.C a*complexityShift c (PowerSeries.X*(f*g))) L (1/h)| ≤
      |a|/|h-c| *|x*y-truncationValue (f*g) (L-1) (1/(h-c))|+
      |a| *|truncationValue (PowerSeries.X*(f*g)) L (1/(h-c))-
        truncationValue (complexityShift c (PowerSeries.X*(f*g))) L (1/h)|:=by
  rw[exact_loss_one_remainder_identity x y a c h f g L hL]
  apply (abs_add_le _ _).trans_eq
  rw[abs_mul,abs_div,abs_mul]

lemma zero_constant_left_product_remainder_norm_le (x y t:ℝ) (f g:Series) (L:ℕ)
    (hL:1 ≤ L) (hf:PowerSeries.coeff 0 f=0) :
    |x*y-truncationValue (f*g) L t| ≤ |x-truncationValue f L t| *|y|+
      ∑i∈Finset.range (L-1),|PowerSeries.coeff (i+1) f| *|t|^(i+1)*
        |y-truncationValue g (L-(i+1)) t|:=by
  have hn:=exact_product_remainder_norm_le x y f g L t
  simp only[Real.norm_eq_abs] at hn
  have hs:(∑i∈Finset.range L,|PowerSeries.coeff i f| *|t|^i*|y-truncationValue g (L-i) t|)=
      ∑i∈Finset.range (L-1),|PowerSeries.coeff (i+1) f| *|t|^(i+1)*|y-truncationValue g (L-(i+1)) t|:=by
    conv_lhs=>rw[show L=(L-1)+1 by omega]
    rw[Finset.sum_range_succ']
    simp only[hf,abs_zero,zero_mul,add_zero,Nat.sub_add_cancel hL]
  rw[hs] at hn
  exact hn

end WP.HigherOrder
