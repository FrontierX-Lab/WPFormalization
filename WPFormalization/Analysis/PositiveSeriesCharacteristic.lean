import Mathlib
noncomputable section
set_option maxHeartbeats 1500000
namespace WP.PositiveConvolution
lemma positive_series_character_deficit (a:ℕ→ℝ) (x:ℝ) (hx:0 ≤ x)
    (ha:∀n,0 ≤ a n) (z F:ℂ) (M:ℝ) (hz:‖z‖=x)
    (hc:HasSum (fun n=>Complex.ofReal (a n)*z^n) F)
    (hr:HasSum (fun n=>a n*x^n) M):
    ‖F‖^2 ≤ M^2-2*a 0*a 1*(x-z.re):=by
  have htailC:Summable (fun n:ℕ=>Complex.ofReal (a (n+2))*z^(n+2)):=
    (summable_nat_add_iff 2).mpr hc.summable
  have htailR:Summable (fun n:ℕ=>a (n+2)*x^(n+2)):=
    (summable_nat_add_iff 2).mpr hr.summable
  let T:ℝ:=∑'n:ℕ,a (n+2)*x^(n+2)
  let G:ℂ:=∑'n:ℕ,Complex.ofReal (a (n+2))*z^(n+2)
  have hT:0 ≤ T:=tsum_nonneg (fun n=>mul_nonneg (ha _) (pow_nonneg hx _))
  have hG:‖G‖ ≤ T:=by
    apply htailC.hasSum.norm_le_of_bounded htailR.hasSum
    intro n
    simp only[norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha _),norm_pow,hz]
    exact le_rfl
  have hF:F=Complex.ofReal (a 0)+Complex.ofReal (a 1)*z+G:=by
    have hh:=hc.summable.sum_add_tsum_nat_add 2
    rw[hc.tsum_eq] at hh
    simpa only[Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,mul_one,G] using hh.symm
  have hM:M=a 0+a 1*x+T:=by
    have hh:=hr.summable.sum_add_tsum_nat_add 2
    rw[hr.tsum_eq] at hh
    simpa only[Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,mul_one,T] using hh.symm
  let B:ℂ:=Complex.ofReal (a 0)+Complex.ofReal (a 1)*z
  let m:ℝ:=a 0+a 1*x
  have hB:‖B‖ ≤ m:=by
    calc
      ‖B‖ ≤ ‖Complex.ofReal (a 0)‖+‖Complex.ofReal (a 1)*z‖:=norm_add_le _ _
      _ = m:=by simp only[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha _),norm_mul,hz,m]
  have hFbound:‖F‖ ≤ ‖B‖+T:=by
    change F=B+G at hF
    rw[hF]
    linarith[norm_add_le B G]
  have hnorm:z.re^2+z.im^2=x^2:=by
    have hh:=Complex.sq_norm z
    rw[hz,Complex.normSq_apply] at hh
    nlinarith
  have hBsq:‖B‖^2=m^2-2*a 0*a 1*(x-z.re):=by
    dsimp only[B,m]
    rw[Complex.sq_norm,Complex.normSq_apply]
    simp only[Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero,
      Complex.add_im,Complex.mul_im,zero_mul,zero_add]
    nlinarith[congrArg (fun t:ℝ=>(a 1)^2*t) hnorm]
  have hp:0 ≤ T*(m-‖B‖):=mul_nonneg hT (sub_nonneg.mpr hB)
  have hsq:‖F‖^2 ≤ (‖B‖+T)^2:=sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) hT) |>.mpr hFbound
  change M=a 0+a 1*x+T at hM
  have hm:M=m+T:=hM
  calc
    _ ≤ (‖B‖+T)^2 := hsq
    _ ≤ m^2-2*a 0*a 1*(x-z.re)+2*m*T+T^2 := by rw[←hBsq]; nlinarith only[hp]
    _ = M^2-2*a 0*a 1*(x-z.re) := by rw[hm]; ring
lemma norm_le_exp_of_sq_deficit (u v:ℝ) (hu:0 ≤ u) (hv:0 ≤ v)
    (hs:u^2 ≤ 1-2*v):u ≤ Real.exp (-v):=by
  have he:1-2*v ≤ Real.exp (-v)^2:=by
    have hh:=Real.add_one_le_exp (-2*v)
    have heq : Real.exp (-v)^2 = Real.exp (-2*v) := by rw[←Real.exp_nat_mul]; congr 1 <;> ring
    rw[heq]
    convert hh using 1 <;> ring
  have hp:=Real.exp_pos (-v)
  nlinarith
lemma positive_series_character_exp_bound (a:ℕ→ℝ) (x:ℝ) (hx:0 ≤ x)
    (ha:∀n,0 ≤ a n) (z F:ℂ) (M:ℝ) (hM:0<M) (hz:‖z‖=x)
    (hc:HasSum (fun n=>Complex.ofReal (a n)*z^n) F)
    (hr:HasSum (fun n=>a n*x^n) M):
    ‖F‖/M ≤ Real.exp (-(a 0*a 1*(x-z.re)/M^2)):=by
  have hdef:=positive_series_character_deficit a x hx ha z F M hz hc hr
  have hre:z.re ≤ x:=by simpa only[hz] using Complex.re_le_norm z
  apply norm_le_exp_of_sq_deficit _ _ (div_nonneg (norm_nonneg _) hM.le)
    (div_nonneg (mul_nonneg (mul_nonneg (ha 0) (ha 1)) (sub_nonneg.mpr hre)) (sq_nonneg _))
  rw[div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hM)).2
  field_simp
  nlinarith
end WP.PositiveConvolution
