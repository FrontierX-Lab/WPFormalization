import WPFormalization.HigherOrder.InverseShiftTail
/-! The actual normalized shift-tail estimate used by C.3.
For a+q≤L, c≤L and S≥2L, the entire omitted tail is at most
exp(2δ) S^(2q)/(q! h^q) when S²/h≤δ≤1. The constant is independent
of all integer orders and shifts. This wider valid constant is sufficient
for the uniform remainder conclusion; no order factor is hidden in it. -/
noncomputable section
namespace WP.HigherOrder
lemma inverse_one_sub_pow_le_exp (x:ℝ) (hx:0 ≤ x) (hx2:x ≤ 1/2) (L:ℕ) :
    1/(1-x)^L ≤ Real.exp (2*(L:ℝ)*x) :=by
  have hp:0<1-x:=by linarith
  have hinv:(1-x)⁻¹-1 ≤ 2*x:=by
    rw[inv_eq_one_div]
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hp).2
    nlinarith
  have hlog:-Real.log (1-x) ≤ 2*x:=by
    have hh:=Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw[Real.log_inv] at hh
    exact hh.trans hinv
  have hmain:1/(1-x)^L=Real.exp (-(L:ℝ)*Real.log (1-x)):=by
    rw[neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hp]
    simp only[one_div]
  rw[hmain]
  apply Real.exp_le_exp.mpr
  have hh:=mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg L : (0:ℝ) ≤ L)
  nlinarith
lemma inverse_shift_tail_normalized (a q L:ℕ) (ha:1 ≤ a) (haq:a+q ≤ L)
    (c S h δ:ℝ) (hc:0 ≤ c) (hcL:c ≤ L) (hS:2*(L:ℝ) ≤ S)
    (hh:0<h) (hsmall:S^2/h ≤ δ) (hδ:δ ≤ 1) :
    (∑'k:ℕ,(Nat.choose (a+(q+k)-1) (q+k):ℝ)*(c/h)^(q+k)) ≤
      Real.exp (2*δ)*S^(2*q)/((q.factorial:ℝ)*h^q) :=by
  have hL:1 ≤ L:=by omega
  have hLR:(1:ℝ) ≤ L:=by exact_mod_cast hL
  have hS1:1 ≤ S:=by linarith
  have hS0:0 ≤ S:=by linarith
  have hhSq:S^2 ≤ h:=(div_le_one hh).mp (hsmall.trans hδ)
  have hx0:0 ≤ c/h:=div_nonneg hc hh.le
  have hxhalf:c/h ≤ 1/2:=(div_le_iff₀ hh).2 (by nlinarith)
  have hx1:c/h<1:=by linarith
  have hCL:c*(L:ℝ) ≤ S^2:=by
    have hp:=mul_le_mul_of_nonneg_right hcL (show (0:ℝ) ≤ L by positivity)
    nlinarith
  have haqR:((a+q:ℕ):ℝ) ≤ L:=by exact_mod_cast haq
  have hnx:((a+q:ℕ):ℝ)*(c/h) ≤ δ:=by
    have hp:=mul_le_mul_of_nonneg_right haqR hc
    have hdiv:((a+q:ℕ):ℝ)*c/h ≤ S^2/h:=div_le_div_of_nonneg_right (hp.trans (by simpa only[mul_comm] using hCL)) hh.le
    have he:((a+q:ℕ):ℝ)*(c/h) ≤ S^2/h:=by simpa only[mul_div_assoc] using hdiv
    exact he.trans hsmall
  have hE:1/(1-c/h)^(a+q) ≤ Real.exp (2*δ):=
    (inverse_one_sub_pow_le_exp (c/h) hx0 hxhalf (a+q)).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hchoose:(Nat.choose (a+q-1) q:ℝ) ≤ (L:ℝ)^q/(q.factorial:ℝ):=by
    apply (Nat.choose_le_pow_div q (a+q-1)).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast (show a+q-1 ≤ L by omega)
  have hPref:(Nat.choose (a+q-1) q:ℝ)*(c/h)^q ≤ S^(2*q)/((q.factorial:ℝ)*h^q):=by
    calc
      _ ≤ ((L:ℝ)^q/(q.factorial:ℝ))*(c/h)^q:=
        mul_le_mul_of_nonneg_right hchoose (pow_nonneg hx0 _)
      _=((L:ℝ)*c)^q/((q.factorial:ℝ)*h^q):=by rw[mul_pow,div_pow];ring
      _ ≤ (S^2)^q/((q.factorial:ℝ)*h^q):=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg (by positivity) hc) (by nlinarith[hCL]) q) (by positivity)
      _=_:=by rw[pow_mul]
  have ht:=inverse_shift_tail_le a q ha (c/h) hx0 hx1
  have hprod:=mul_le_mul hPref hE (by positivity:0 ≤ 1/(1-c/h)^(a+q))
    (by positivity:0 ≤ S^(2*q)/((q.factorial:ℝ)*h^q))
  exact ht.trans (by convert hprod using 1 <;>ring)
end WP.HigherOrder
