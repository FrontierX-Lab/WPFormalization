import WPFormalization.HigherOrder.BudgetShiftRemainder
/-! The shift geometry depends only on the parent scale S. The child
coefficient/remainder scale T may be arbitrarily larger. This is essential
for the unbounded degree variable in the actual kernel sum. -/
noncomputable section
namespace WP.HigherOrder
lemma shift_truncation_remainder_bound_budget_two_scale (f:Series)(e:ℕ→ℝ)(q L:ℕ)
    (hL:1 ≤ L)(hq:q ≤ L)(c S T h δ:ℝ)(hc:|c| ≤ L)(hS:2*(L:ℝ) ≤ S)(hST:S ≤ T)(hh:0<h)
    (hsmall:S^2/h ≤ δ)(hδ:δ ≤ 1)(he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i<q → |PowerSeries.coeff i f| ≤ e i*T^(2*i)) :
    |truncationValue f q (1/(h-c))-truncationValue (complexityShift c f) q (1/h)| ≤
      (Real.exp (2*δ)*T^(2*q)/h^q)*(∑i∈Finset.range q,e i/((q-i).factorial:ℝ)) := by
  have hLR:(1:ℝ) ≤ L := by exact_mod_cast hL
  have hS0:0 ≤ S := by linarith
  have hT0:0 ≤ T := hS0.trans hST
  have hhSq:S^2 ≤ h := (div_le_one hh).mp (hsmall.trans hδ)
  have hch:|c|<h := by nlinarith [abs_nonneg c]
  have hhc:0<h-c := by linarith [le_abs_self c]
  have ht:(1/h)/(1-c*(1/h))=1/(h-c) := by field_simp [hh.ne',hhc.ne']
  have hdef:=exact_shift_truncation_defect f c (1/h) q
  rw [ht] at hdef
  rw [hdef]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑i∈Finset.range q,(Real.exp (2*δ)*T^(2*q)/h^q)*(e i/((q-i).factorial:ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hei:0 ≤ e i := he i
      have hiq:i<q := Finset.mem_range.mp hi
      have hqi:1 ≤ q-i := by omega
      have hpow:=inverse_linear_power_truncation_error_normalized i (q-i) L hqi
        (by omega) c S h δ hc hS hh hsmall hδ
      have hiBound:|PowerSeries.coeff i f| * |1/h|^i ≤ e i*T^(2*i)/h^i := by
        rw [abs_of_pos (one_div_pos.mpr hh)]
        convert mul_le_mul_of_nonneg_right (hf i hiq) (pow_nonneg (one_div_pos.mpr hh).le i) using 1 <;>
          rw [div_pow,one_pow] <;> ring
      have hpowT:=hpow.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hST (2*(q-i)))
          (Real.exp_nonneg _))
        (by positivity:0 ≤ ((q-i).factorial:ℝ)*h^(q-i)))
      have hp1:T^(2*i)*T^(2*(q-i))=T^(2*q) := by rw [←pow_add];congr 1;omega
      have hp2:h^i*h^(q-i)=h^q := by rw [←pow_add,Nat.add_sub_of_le hiq.le]
      rw [abs_mul,abs_mul,abs_pow]
      simp only [mul_one_div]
      have hb:=mul_le_mul hiBound hpowT (abs_nonneg _) (by positivity:0 ≤ e i*T^(2*i)/h^i)
      apply hb.trans_eq
      calc
        _=Real.exp (2*δ)*e i*(T^(2*i)*T^(2*(q-i)))/(((q-i).factorial:ℝ)*(h^i*h^(q-i))) := by ring
        _=_ := by rw [hp1,hp2];ring
    _=_ := by rw [Finset.mul_sum]

lemma shifted_remainder_with_budget_two_scale (x E:ℝ)(f:Series)(e:ℕ→ℝ)(q L:ℕ)
    (hq1:1 ≤ q)(hq:q ≤ L)(c S T h δ:ℝ)(hc:|c| ≤ L)(hS:2*(L:ℝ) ≤ S)(hST:S ≤ T)(hh:0<h)
    (hsmall:S^2/h ≤ δ)(hδ:δ ≤ 1)(hE:0 ≤ E)(he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i<q → |PowerSeries.coeff i f| ≤ e i*T^(2*i))
    (hx:|x-truncationValue f q (1/(h-c))| ≤ E*T^(2*q)/(h-c)^q) :
    |x-truncationValue (complexityShift c f) q (1/h)| ≤
      (Real.exp (2*δ)*T^(2*q)/h^q)*(E+∑i∈Finset.range q,e i/((q-i).factorial:ℝ)) := by
  have hL:1 ≤ L := by omega
  have hs0:0 ≤ S := by have hn:=Nat.cast_nonneg (α:=ℝ) L;linarith
  have hd:=shifted_denominator_power_bound q L hq1 hq c S h δ hc hS hh hsmall hδ
  have hactual:|x-truncationValue f q (1/(h-c))| ≤ (Real.exp (2*δ)*T^(2*q)/h^q)*E := by
    apply hx.trans
    calc
      _=E*T^(2*q)*(1/(h-c)^q) := by ring
      _ ≤ E*T^(2*q)*(Real.exp (2*δ)/h^q) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hE (pow_nonneg (hs0.trans hST) _))
      _=_ := by ring
  have ht:=shift_truncation_remainder_bound_budget_two_scale f e q L hL hq c S T h δ hc hS hST hh hsmall hδ he hf
  calc
    _ ≤ |x-truncationValue f q (1/(h-c))|+
        |truncationValue f q (1/(h-c))-truncationValue (complexityShift c f) q (1/h)| := abs_sub_le _ _ _
    _ ≤ (Real.exp (2*δ)*T^(2*q)/h^q)*E+
        (Real.exp (2*δ)*T^(2*q)/h^q)*(∑i∈Finset.range q,e i/((q-i).factorial:ℝ)) := add_le_add hactual ht
    _=_ := by ring

end WP.HigherOrder
