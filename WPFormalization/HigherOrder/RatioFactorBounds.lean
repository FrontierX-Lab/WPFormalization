import WPFormalization.HigherOrder.ShiftExtraction
import WPFormalization.HigherOrder.ActualRatioRemainder
import WPFormalization.HigherOrder.ScalarScaledRemainders
import WPFormalization.HigherOrder.ProductCoefficientBounds
/-! Finite known-coefficient bounds and the genuine shifted scalar /
inverse-linear remainder. The number of factors costs a fixed exponential,
while the retained coefficient degree keeps its exact S^(2i) weight.
Every displayed error term is linear in one child scalar remainder. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma factorial_convolution_geometric_bound (C B:ℝ)(hC:0 ≤ C)(hB:0 ≤ B)(q:ℕ) :
    (∑i∈Finset.range q,C*B^i/((q-i).factorial:ℝ)) ≤ C*(2*max B 1)^q := by
  let R:=max B 1
  have hR:1 ≤ R:=le_max_right _ _
  have hR0:0 ≤ R:=by linarith
  have hterm(i:ℕ)(hi:i∈Finset.range q):C*B^i/((q-i).factorial:ℝ) ≤ C*R^q:=by
    have hiq:i ≤ q:=(Finset.mem_range.mp hi).le
    have hBP:B^i ≤ R^q:=(pow_le_pow_left₀ hB (le_max_left _ _) i).trans (pow_le_pow_right₀ hR hiq)
    calc
      _ ≤ C*B^i:=div_le_self (by positivity) (by exact_mod_cast (show 1 ≤ (q-i).factorial by have := Nat.factorial_pos (q-i);omega))
      _ ≤ C*R^q:=mul_le_mul_of_nonneg_left hBP hC
  apply (Finset.sum_le_sum hterm).trans
  simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hn:(q:ℝ) ≤ 2^q:=by exact_mod_cast Nat.le_of_lt q.lt_two_pow_self
  have hb:=mul_le_mul_of_nonneg_right hn (mul_nonneg hC (pow_nonneg hR0 q))
  convert hb using 1 <;>dsimp[R]<;>rw[mul_pow]<;>ring

lemma factorial_convolution_geometric_bound_succ (C B:ℝ)(hC:0 ≤ C)(hB:0 ≤ B)(i:ℕ) :
    (∑a∈Finset.range (i+1),C*B^a/((i-a).factorial:ℝ)) ≤ (2*C)*(2*max B 1)^i := by
  let R:=max B 1
  have hR:1 ≤ R:=le_max_right _ _
  have hR0:0 ≤ R:=by linarith
  have hterm(a:ℕ)(ha:a∈Finset.range (i+1)):C*B^a/((i-a).factorial:ℝ) ≤ C*R^i:=by
    have hai:a ≤ i:=by have :=Finset.mem_range.mp ha;omega
    have hBP:B^a ≤ R^i:=(pow_le_pow_left₀ hB (le_max_left _ _) a).trans (pow_le_pow_right₀ hR hai)
    exact (div_le_self (by positivity) (by exact_mod_cast (show 1 ≤ (i-a).factorial by have := Nat.factorial_pos (i-a);omega))).trans
      (mul_le_mul_of_nonneg_left hBP hC)
  apply (Finset.sum_le_sum hterm).trans
  simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hn:((i+1:ℕ):ℝ) ≤ 2^(i+1):=by exact_mod_cast Nat.le_of_lt (i+1).lt_two_pow_self
  have hb:=mul_le_mul_of_nonneg_right hn (mul_nonneg hC (pow_nonneg hR0 i))
  convert hb using 1 <;>dsimp[R]<;>rw[mul_pow,pow_succ]<;>ring

lemma shifted_scalar_inverse_linear_coeff_exponential (f:Series)(C B:ℝ)(hC:0 ≤ C)(hB:0 ≤ B)
    (K L:ℕ)(hKL:K+1 ≤ L)(c S:ℝ)(hc:|c| ≤ L)(hS:(L:ℝ) ≤ S)
    (hf:∀i ≤ K,|PowerSeries.coeff i f| ≤ C*B^i*S^(2*i)) :
    |PowerSeries.coeff K (complexityShift c f*(1-PowerSeries.C c*PowerSeries.X)⁻¹)| ≤
      (2*(max 1 (2*C))^2)*(4*max B 1)^K*S^(2*K) := by
  let R:=2*max B 1
  let A:=max 1 (2*C)
  have hA:1 ≤ A:=le_max_left _ _
  have hA0:0 ≤ A:=by linarith
  have hR:1 ≤ R:=by dsimp[R];have :=le_max_right B 1;linarith
  have hR0:0 ≤ R:=by linarith
  have hS0:0 ≤ S:=(Nat.cast_nonneg L).trans hS
  have hshift:∀i ≤ K,|PowerSeries.coeff i (complexityShift c f)| ≤ A*R^i*S^(2*i):=by
    intro i hi
    have hb:=complexityShift_coeff_scaled_bound c S f (fun i=>C*B^i) i L (by omega) hc hS
      (fun a=>mul_nonneg hC (pow_nonneg hB _)) (fun a ha=>hf a (by omega))
    have he:=factorial_convolution_geometric_bound_succ C B hC hB i
    have hp: (∑a∈Finset.range (i+1),C*B^a/((i-a).factorial:ℝ)) ≤ A*R^i:=
      he.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hR0 i))
    apply hb.trans
    convert mul_le_mul_of_nonneg_left hp (pow_nonneg hS0 (2*i)) using 1 <;>ring
  have hinv:∀i ≤ K,|PowerSeries.coeff i ((1-PowerSeries.C c*PowerSeries.X)⁻¹:Series)| ≤ A*R^i*S^(2*i):=by
    intro i hi
    have hb:=inverse_linear_pow_coeff_normalized_all c S 1 i L (by omega) hc hS
    simp only[pow_one] at hb
    have hd:S^(2*i)/(i.factorial:ℝ) ≤ S^(2*i):=
      div_le_self (pow_nonneg hS0 _) (by exact_mod_cast (show 1 ≤ i.factorial by have :=Nat.factorial_pos i;omega))
    have hAR:1 ≤ A*R^i:=one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hR)
    exact (hb.trans hd).trans (by nlinarith[pow_nonneg hS0 (2*i)])
  have hb:=product_coeff_scaled_exponential (complexityShift c f)
    ((1-PowerSeries.C c*PowerSeries.X)⁻¹) K A R S hA0 hR0 hS0 hshift hinv
  apply hb.trans_eq
  rw[max_eq_left hR]
  dsimp[R,A]
  congr 2
  ring

lemma finite_geometric_two_le (n:ℕ) : (∑a∈Finset.range (n+1),(2:ℝ)^a) ≤ 2^(n+1) := by
  induction n with
  | zero=>norm_num
  | succ n ih=>
    rw[Finset.sum_range_succ,pow_succ (2:ℝ) (n+1)]
    linarith

lemma finite_product_coeff_geometric (f:ℕ→PowerSeries ℝ)(n q:ℕ)(C B S:ℝ)
    (hC:0 ≤ C)(hB:0 ≤ B)(hS:0 ≤ S)
    (hf:∀a<n,∀i ≤ q,|PowerSeries.coeff i (f a)| ≤ C*B^i*S^(2*i)) :
    ∀i ≤ q,|PowerSeries.coeff i (∏a∈Finset.range n,f a)| ≤
      (2*C)^n*(2*B)^i*S^(2*i) := by
  induction n with
  | zero=>
    intro i hi
    simp only[Finset.prod_range_zero,pow_zero,one_mul,PowerSeries.coeff_one]
    split_ifs with hz
    · subst i;norm_num
    · simp only[abs_zero];positivity
  | succ n ih=>
    intro i hi
    rw[Finset.prod_range_succ,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hterm(a:ℕ)(ha:a∈Finset.range (i+1)):
        |PowerSeries.coeff a (∏k∈Finset.range n,f k)*PowerSeries.coeff (i-a) (f n)| ≤
        ((2*C)^n*C*B^i*S^(2*i))*(2:ℝ)^a := by
      have hai:a ≤ i:=by have :=Finset.mem_range.mp ha;omega
      rw[abs_mul]
      have hpre:=ih (fun b hb=>hf b (by omega)) a (by omega)
      have hnew:=hf n (by omega) (i-a) (by omega)
      apply (mul_le_mul hpre hnew (abs_nonneg _) (by positivity)).trans_eq
      have hpB:B^a*B^(i-a)=B^i:=by rw[←pow_add,Nat.add_sub_of_le hai]
      have hpS:S^(2*a)*S^(2*(i-a))=S^(2*i):=by rw[←pow_add];congr 1;omega
      simp only[mul_pow]
      calc
        _=(2*C)^n*C*(B^a*B^(i-a))*(S^(2*a)*S^(2*(i-a)))*2^a:=by ring
        _=_:=by rw[hpB,hpS,mul_pow]
    apply (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans _)
    rw[←Finset.mul_sum]
    have hb:=mul_le_mul_of_nonneg_left (finite_geometric_two_le i)
      (by positivity:0 ≤ (2*C)^n*C*B^i*S^(2*i))
    apply hb.trans_eq
    rw[pow_succ,mul_pow]
    ring

lemma shifted_scalar_inverse_linear_remainder (x E:ℝ)(f:Series)(e:ℕ→ℝ)(q L:ℕ)
    (hq1:1 ≤ q)(hqL:q+1 ≤ L)(c S h δ:ℝ)(hc:|c| ≤ L)(hS:2*(L:ℝ) ≤ S)(hh:0<h)
    (hsmall:S^2/h ≤ δ)(hδ:δ ≤ 1)(hE:0 ≤ E)(he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i<q → |PowerSeries.coeff i f| ≤ e i*S^(2*i))
    (hx:|x-truncationValue f q (1/(h-c))| ≤ E*S^(2*q)/(h-c)^q) :
    |x/(1-c/h)-truncationValue (complexityShift c f*(1-C c*PowerSeries.X)⁻¹) q (1/h)| ≤
      (S^(2*q)/h^q)*Real.exp (2*δ)*
        (2*(E+∑i∈Finset.range q,e i/((q-i).factorial:ℝ))+
          ∑i∈Finset.range q,(∑a∈Finset.range (i+1),e a/((i-a).factorial:ℝ))/((q-i).factorial:ℝ)) := by
  have hL:1 ≤ L := by omega
  have hS0:0 ≤ S := by have h:=Nat.cast_nonneg (α:=ℝ) L;linarith
  let es:ℕ→ℝ:=fun i=>∑a∈Finset.range (i+1),e a/((i-a).factorial:ℝ)
  let ei:ℕ→ℝ:=fun m=>Real.exp (2*δ)/(m.factorial:ℝ)
  let R:=Real.exp (2*δ)*(E+∑i∈Finset.range q,e i/((q-i).factorial:ℝ))
  have hes:∀i,0 ≤ es i:=by intro i;exact Finset.sum_nonneg (fun a ha=>div_nonneg (he a) (Nat.cast_nonneg _))
  have hei:∀i,0 ≤ ei i:=by intro i;dsimp[ei];positivity
  have hR:0 ≤ R:=mul_nonneg (Real.exp_nonneg _) (add_nonneg hE
    (Finset.sum_nonneg (fun i hi=>div_nonneg (he i) (Nat.cast_nonneg _))))
  have hX:|(1-c/h)⁻¹| ≤ 2:=ratio_inverse_linear_abs_bound L hL c S h hc hS hh (hsmall.trans hδ)
  have hshift:=shifted_remainder_with_budget x E f e q L hq1 (by omega) c S h δ hc hS hh hsmall hδ hE he hf hx
  have hshift':|x-truncationValue (complexityShift c f) q (1/h)| ≤ R*S^(2*q)/h^q:=by
    convert hshift using 1 <;>dsimp[R]<;>ring
  have hscoeff:∀i<q,|PowerSeries.coeff i (complexityShift c f)| ≤ es i*S^(2*i):=by
    intro i hi
    have hb:=complexityShift_coeff_scaled_bound c S f e i L (by omega) hc (by linarith) he
      (fun a ha=>hf a (by omega))
    convert hb using 1 <;>dsimp[es]<;>ring
  have hierr:∀m:ℕ,1 ≤ m→m ≤ q→
      |(1-c/h)⁻¹-truncationValue ((1-C c*PowerSeries.X)⁻¹) m (1/h)| ≤ ei m*S^(2*m)/h^m:=by
    intro m hm hmq
    have hb:=inverse_linear_power_truncation_error_normalized 1 m L hm (by omega) c S h δ hc hS hh hsmall hδ
    simp only[pow_one,one_div] at hb
    calc
      _ ≤ Real.exp (2*δ)*S^(2*m)/((m.factorial:ℝ)*h^m):=by simpa only[one_div] using hb
      _=_:=by dsimp[ei];ring
  have hb:=product_remainder_scaled_bound_uniform x (1-c/h)⁻¹ (complexityShift c f)
    ((1-C c*PowerSeries.X)⁻¹) q hq1 S h 2 R es ei hS0 hh (by norm_num) hR hes hei hX hshift' hscoeff hierr
  rw[div_eq_mul_inv]
  apply hb.trans_eq
  have hsume:(∑i∈Finset.range q,es i*ei (q-i))=
      Real.exp (2*δ)*(∑i∈Finset.range q,es i/((q-i).factorial:ℝ)):=by
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp[ei]
    ring
  rw[hsume]
  dsimp[R,es]
  ring

lemma shifted_scalar_inverse_linear_remainder_exponential (x E:ℝ)(f:Series)(C B:ℝ)
    (hC:0 ≤ C)(hB:0 ≤ B)(q L:ℕ)(hq1:1 ≤ q)(hqL:q+1 ≤ L)
    (c S h δ:ℝ)(hc:|c| ≤ L)(hS:2*(L:ℝ) ≤ S)(hh:0<h)
    (hsmall:S^2/h ≤ δ)(hδ:δ ≤ 1)(hE:0 ≤ E)
    (hf:∀i:ℕ,i<q → |PowerSeries.coeff i f| ≤ C*B^i*S^(2*i))
    (hx:|x-truncationValue f q (1/(h-c))| ≤ E*S^(2*q)/(h-c)^q) :
    |x/(1-c/h)-truncationValue (complexityShift c f*(1-PowerSeries.C c*PowerSeries.X)⁻¹) q (1/h)| ≤
      (S^(2*q)/h^q)*(2*Real.exp 2*E+(4*C*Real.exp 2)*(4*max B 1)^q) := by
  let R:=max B 1
  have hR:1 ≤ R:=le_max_right _ _
  have hR0:0 ≤ R:=by linarith
  have he:∀i:ℕ,0 ≤ C*B^i:=fun i=>mul_nonneg hC (pow_nonneg hB _)
  have hb:=shifted_scalar_inverse_linear_remainder x E f (fun i=>C*B^i) q L hq1 hqL
    c S h δ hc hS hh hsmall hδ hE he hf hx
  have hfirst:(∑i∈Finset.range q,C*B^i/((q-i).factorial:ℝ)) ≤ C*(4*R)^q:=
    (factorial_convolution_geometric_bound C B hC hB q).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity:0 ≤ 2*R) (by linarith) q) hC)
  have hsecond:(∑i∈Finset.range q,(∑a∈Finset.range (i+1),C*B^a/((i-a).factorial:ℝ))/((q-i).factorial:ℝ)) ≤
      (2*C)*(4*R)^q:=by
    apply (Finset.sum_le_sum (fun i hi=>div_le_div_of_nonneg_right
      (factorial_convolution_geometric_bound_succ C B hC hB i) (Nat.cast_nonneg _))).trans
    have h:=factorial_convolution_geometric_bound (2*C) (2*R) (by positivity) (by positivity) q
    rw[max_eq_left (by linarith:1 ≤ 2*R)] at h
    convert h using 1 <;>dsimp[R]<;>ring
  have hknown:2*(E+∑i∈Finset.range q,C*B^i/((q-i).factorial:ℝ))+
      (∑i∈Finset.range q,(∑a∈Finset.range (i+1),C*B^a/((i-a).factorial:ℝ))/((q-i).factorial:ℝ)) ≤
      2*E+4*C*(4*R)^q:=by linarith
  have hknown0:0 ≤ 2*E+4*C*(4*R)^q:=by positivity
  have hExp:Real.exp (2*δ) ≤ Real.exp 2:=Real.exp_le_exp.mpr (by linarith)
  have hlast:=mul_le_mul hExp hknown (by positivity) (Real.exp_nonneg 2)
  have hS0:0 ≤ S:=by have :=Nat.cast_nonneg (α:=ℝ) L;linarith
  apply hb.trans
  have hmul:=mul_le_mul_of_nonneg_left hlast (by positivity:0 ≤ S^(2*q)/h^q)
  convert hmul using 1 <;> (try dsimp[R]) <;>ring

end WP.HigherOrder
