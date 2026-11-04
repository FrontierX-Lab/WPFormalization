import WPFormalization.HigherOrder.LinearRemainderAlgebra
/-! Sharp loss-one remainders retain S^(2(L-1)) before the actual finite
label and canonical path counts. The shift tail and child-complexity
comparison have one uniform exp(2δ) factor, independent of all orders. -/
noncomputable section
namespace WP.HigherOrder
lemma loss_one_shift_truncation_bound (f:Series) (e:ℕ→ℝ) (L:ℕ) (hL:1 ≤ L)
    (c S h δ:ℝ) (hc:|c| ≤ L) (hS:2*(L:ℝ) ≤ S) (hh:0<h)
    (hsmall:S^2/h ≤ δ) (hδ:δ ≤ 1) (he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i<L-1→|PowerSeries.coeff i f| ≤ e i*S^(2*i)) :
    |truncationValue (PowerSeries.X*f) L (1/(h-c))-
      truncationValue (complexityShift c (PowerSeries.X*f)) L (1/h)| ≤
      (Real.exp (2*δ)*S^(2*(L-1))/h^L)*(∑i∈Finset.range (L-1),e i/((L-1-i).factorial:ℝ)) :=by
  have hLR:(1:ℝ) ≤ L:=by exact_mod_cast hL
  have hSp:0<S:=by linarith
  let e':ℕ→ℝ:=fun i=>if i=0 then 0 else e (i-1)/S^2
  have he':∀i:ℕ,0 ≤ e' i:=by
    intro i
    dsimp[e']
    split_ifs
    · exact le_rfl
    · exact div_nonneg (he _) (sq_nonneg _)
  have hf':∀i:ℕ,i<L→|PowerSeries.coeff i (PowerSeries.X*f)| ≤ e' i*S^(2*i):=by
    intro i hi
    cases i with
    | zero=>
      have hzero:PowerSeries.coeff 0 (PowerSeries.X*f)=0:=by
        simp only[PowerSeries.coeff_zero_eq_constantCoeff,map_mul,PowerSeries.constantCoeff_X,zero_mul]
      simp only[hzero,abs_zero,e',if_pos rfl,zero_mul]
      exact le_rfl
    | succ i=>
      have hcoef:=PowerSeries.coeff_X_pow_mul f 1 i
      simp only[pow_one] at hcoef
      rw[hcoef]
      apply (hf i (by omega)).trans_eq
      simp only[e',Nat.succ_ne_zero,if_false,Nat.add_sub_cancel]
      have hp:S^(2*(i+1))=S^(2*i)*S^2:=by rw[show 2*(i+1)=2*i+2 by omega,pow_add]
      rw[hp]
      field_simp[hSp.ne']
  have hb:=shift_truncation_remainder_bound (PowerSeries.X*f) e' L hL c S h δ hc hS hh hsmall hδ he' hf'
  have hsum:(∑i∈Finset.range L,e' i/((L-i).factorial:ℝ))=
      (1/S^2)*(∑i∈Finset.range (L-1),e i/((L-1-i).factorial:ℝ)):=by
    cases L with
    | zero=>omega
    | succ q=>
      rw[Finset.sum_range_succ']
      simp only[e',if_pos rfl,zero_div,add_zero,Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
      rw[Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only[Nat.succ_ne_zero,if_false,Nat.add_sub_cancel]
      ring
  rw[hsum] at hb
  apply hb.trans_eq
  have hp:S^(2*L)=S^2*S^(2*(L-1)):=by rw[←pow_add];congr 1;omega
  rw[hp]
  field_simp[hSp.ne',pow_ne_zero _ hh.ne']
lemma shifted_denominator_power_bound (q L:ℕ) (hq:1 ≤ q) (hqL:q ≤ L)
    (c S h δ:ℝ) (hc:|c| ≤ L) (hS:2*(L:ℝ) ≤ S)
    (hh:0<h) (hsmall:S^2/h ≤ δ) (hδ:δ ≤ 1) :
    1/(h-c)^q ≤ Real.exp (2*δ)/h^q :=by
  have hL:1 ≤ L:=by omega
  have hLR:(1:ℝ) ≤ L:=by exact_mod_cast hL
  have hS1:1 ≤ S:=by linarith
  have hhSq:S^2 ≤ h:=(div_le_one hh).mp (hsmall.trans hδ)
  have hch:|c|<h:=by nlinarith[abs_nonneg c]
  have hcden:0<h-|c|:=by linarith
  have hcpos:0<h-c:=by linarith[le_abs_self c]
  have hx0:0 ≤ |c|/h:=div_nonneg (abs_nonneg _) hh.le
  have hxhalf:|c|/h ≤ 1/2:=(div_le_iff₀ hh).2 (by nlinarith[abs_nonneg c])
  have hqR:(q:ℝ) ≤ L:=by exact_mod_cast hqL
  have hCL:((q:ℝ)*|c|) ≤ S^2:=by
    have hp:=mul_le_mul hqR hc (abs_nonneg c) (by positivity:(0:ℝ) ≤ L)
    nlinarith
  have hnx:(q:ℝ)*(|c|/h) ≤ δ:=by
    have he:((q:ℝ)*|c|)/h ≤ S^2/h:=div_le_div_of_nonneg_right hCL hh.le
    exact (show (q:ℝ)*(|c|/h) ≤ S^2/h by simpa only[mul_div_assoc] using he).trans hsmall
  have hE:1/(1-|c|/h)^q ≤ Real.exp (2*δ):=
    (inverse_one_sub_pow_le_exp (|c|/h) hx0 hxhalf q).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hfact:h-|c|=h*(1-|c|/h):=by field_simp[hh.ne']
  calc
    _ ≤ 1/(h-|c|)^q:=one_div_le_one_div_of_le (pow_pos hcden _)
      (pow_le_pow_left₀ hcden.le (by linarith[le_abs_self c]) _)
    _=(1/(1-|c|/h)^q)/h^q:=by rw[hfact,mul_pow];ring
    _ ≤ _:=div_le_div_of_nonneg_right hE (pow_nonneg hh.le _)
lemma loss_one_atom_remainder_scaled_bound (x y a A₀ c S T h δ Rq:ℝ)
    (f g:Series) (e:ℕ→ℝ) (L:ℕ) (hL:1 ≤ L) (hA₀:0 ≤ A₀) (ha:|a| ≤ A₀)
    (hc:|c| ≤ L) (hS:2*(L:ℝ) ≤ S) (hT:0 ≤ T) (hh:0<h)
    (hsmall:S^2/h ≤ δ) (hδ:δ ≤ 1) (hRq:0 ≤ Rq) (he:∀i:ℕ,0 ≤ e i)
    (hproduct:|x*y-truncationValue (f*g) (L-1) (1/(h-c))| ≤
      Rq*T^(2*(L-1))/(h-c)^(L-1))
    (hcoeff:∀i:ℕ,i<L-1→|PowerSeries.coeff i (f*g)| ≤ e i*T^(2*i)) :
    |a/(h-c)*(x*y)-truncationValue (PowerSeries.C a*complexityShift c (PowerSeries.X*(f*g))) L (1/h)| ≤
      (A₀*Real.exp (2*δ)/h^L)*(Rq*T^(2*(L-1))+
        S^(2*(L-1))*(∑i∈Finset.range (L-1),e i*T^(2*i)/(S^(2*i)*((L-1-i).factorial:ℝ)))) :=by
  have hLR:(1:ℝ) ≤ L:=by exact_mod_cast hL
  have hSp:0<S:=by linarith
  have hhSq:S^2 ≤ h:=(div_le_one hh).mp (hsmall.trans hδ)
  have hch:|c|<h:=by nlinarith[abs_nonneg c]
  have hcpos:0<h-c:=by linarith[le_abs_self c]
  have hpow:(h-c)*(h-c)^(L-1)=(h-c)^L:=by rw[←pow_succ',Nat.sub_add_cancel hL]
  have hden:=shifted_denominator_power_bound L L hL le_rfl c S h δ hc hS hh hsmall hδ
  have hfirst:|a|/|h-c| *|x*y-truncationValue (f*g) (L-1) (1/(h-c))| ≤
      (A₀*Real.exp (2*δ)/h^L)*(Rq*T^(2*(L-1))):=by
    rw[abs_of_pos hcpos]
    have hf:=mul_le_mul (div_le_div_of_nonneg_right ha hcpos.le) hproduct (abs_nonneg _)
      (by positivity:0 ≤ A₀/(h-c))
    have hfact:(A₀/(h-c))*(Rq*T^(2*(L-1))/(h-c)^(L-1))=
        (A₀*Rq*T^(2*(L-1)))*(1/(h-c)^L):=by
      calc
        _=A₀*Rq*T^(2*(L-1))/((h-c)*(h-c)^(L-1)):=by rw[div_mul_div_comm];ring
        _=_:=by rw[hpow];ring
    rw[hfact] at hf
    exact hf.trans ((mul_le_mul_of_nonneg_left hden (by positivity)).trans_eq (by ring))
  let e':ℕ→ℝ:=fun i=>e i*T^(2*i)/S^(2*i)
  have he':∀i:ℕ,0 ≤ e' i:=by
    intro i
    have hei:=he i
    dsimp[e']
    positivity
  have hcoeff':∀i:ℕ,i<L-1→|PowerSeries.coeff i (f*g)| ≤ e' i*S^(2*i):=by
    intro i hi
    apply (hcoeff i hi).trans_eq
    dsimp[e']
    field_simp[hSp.ne']
  have hshift:=loss_one_shift_truncation_bound (f*g) e' L hL c S h δ hc hS hh hsmall hδ he' hcoeff'
  have hshift0:0 ≤ (Real.exp (2*δ)*S^(2*(L-1))/h^L)*
      (∑i∈Finset.range (L-1),e' i/((L-1-i).factorial:ℝ)):=by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i hi=>div_nonneg (he' i) (by positivity))
  have hsecond:|a| *|truncationValue (PowerSeries.X*(f*g)) L (1/(h-c))-
      truncationValue (complexityShift c (PowerSeries.X*(f*g))) L (1/h)| ≤
      (A₀*Real.exp (2*δ)/h^L)*S^(2*(L-1))*
        (∑i∈Finset.range (L-1),e i*T^(2*i)/(S^(2*i)*((L-1-i).factorial:ℝ))):=by
    apply (mul_le_mul ha hshift (abs_nonneg _) hA₀).trans_eq
    have hsum:(∑i∈Finset.range (L-1),e' i/((L-1-i).factorial:ℝ))=
        ∑i∈Finset.range (L-1),e i*T^(2*i)/(S^(2*i)*((L-1-i).factorial:ℝ)):=by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp[e']
      ring
    rw[hsum]
    ring
  have hb:=loss_one_remainder_bound x y a c h f g L hL
  exact hb.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

lemma mixed_scale_convolution_bound (S T:ℝ) (hS:0<S) (hST:S ≤ T) (q:ℕ)
    (e:ℕ→ℝ) (he:∀i:ℕ,0 ≤ e i) :
    S^(2*q)*(∑i∈Finset.range q,e i*T^(2*i)/(S^(2*i)*((q-i).factorial:ℝ))) ≤
      T^(2*q)*(∑i∈Finset.range q,e i/((q-i).factorial:ℝ)):=by
  simp only[Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hiq:i ≤ q:=(Finset.mem_range.mp hi).le
  have hpS:S^(2*q)=S^(2*i)*S^(2*(q-i)):=by rw[←pow_add];congr 1;omega
  have hpT:T^(2*(q-i))*T^(2*i)=T^(2*q):=by rw[←pow_add];congr 1;omega
  calc
    _=e i*(S^(2*(q-i))*T^(2*i))/((q-i).factorial:ℝ):=by
      rw[hpS]
      field_simp[hS.ne']
    _ ≤ e i*(T^(2*(q-i))*T^(2*i))/((q-i).factorial:ℝ):=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hS.le hST _) (pow_nonneg (hS.le.trans hST) _)) (he i)) (by positivity)
    _=_:=by rw[hpT];ring

end WP.HigherOrder
