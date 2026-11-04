import Mathlib
/-! The linear error majorant in the final C.3 induction.
Four actual stage inequalities reduce algebraically to one positive
convolution. An explicit geometric bound follows by strong induction from
exponential forcing and kernel coefficients. The recurrence hypotheses are
helper inputs to be supplied by the proved actual operators, not external
mathematics or an assertion of the unfinished C.3 remainder target. -/
noncomputable section
namespace WP.HigherOrder
lemma sum_Icc_geom_le_two_mul (r:ℝ) (n:ℕ) (hr:0 ≤ r) (hr2:r ≤ 1/2) :
    (∑i∈Finset.Icc 1 n,r^i) ≤ 2*r := by
  have he : (∑i∈Finset.Icc 1 n,r^i)=r*(∑j∈Finset.range n,r^j) := by
    rw[Finset.mul_sum]
    apply Finset.sum_bij (fun i _=>i-1)
    · intro i hi
      obtain ⟨h1,h2⟩:=Finset.mem_Icc.mp hi
      exact Finset.mem_range.mpr (by omega)
    · intro i hi j hj h
      obtain ⟨h1,h2⟩:=Finset.mem_Icc.mp hi
      obtain ⟨h3,h4⟩:=Finset.mem_Icc.mp hj
      omega
    · intro j hj
      have hj':=Finset.mem_range.mp hj
      refine ⟨j+1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
    · intro i hi
      obtain ⟨h1,h2⟩:=Finset.mem_Icc.mp hi
      calc
        _=r^(i-1+1):=by congr 1;omega
        _=r*r^(i-1):=by rw[pow_succ];ring
  rw[he]
  calc
    _ ≤ r*(∑j∈Finset.range n,(1/(2:ℝ))^j):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj=>pow_le_pow_left₀ hr hr2 j)) hr
    _ ≤ r*2:=mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hr
    _=2*r:=by ring

lemma linear_error_majorant_bound (e f k:ℕ → ℝ) (A F B K C Q:ℝ)
    (hA:0 ≤ A) (hF:0 ≤ F) (hB:0<B) (hK:0 ≤ K) (hC:0 ≤ C) (hQ:0<Q)
    (hBq:2*B ≤ Q) (hres:4*A*K*B ≤ Q) (hforce:2*A*F ≤ C)
    (hk0:∀i:ℕ,0 ≤ k i) (hkb:∀i:ℕ,1 ≤ i → k i ≤ K*B^i)
    (hfb:∀n:ℕ,f n ≤ F*B^n) (h0:e 0 ≤ C) (h1:e 1 ≤ C*Q)
    (hrec:∀n:ℕ,2 ≤ n → e n ≤ A*f n+A*∑i∈Finset.Icc 1 n,k i*e (n-i)) :
    ∀n:ℕ,e n ≤ C*Q^n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn0:n=0
    · subst n;simpa only[pow_zero,mul_one] using h0
    by_cases hn1:n=1
    · subst n;simpa only[pow_one] using h1
    have hn2:2 ≤ n:=by omega
    have hratio:0 ≤ B/Q:=div_nonneg hB.le hQ.le
    have hratio2:B/Q ≤ 1/2:=(div_le_iff₀ hQ).mpr (by linarith)
    have hterm (i:ℕ) (hi:i∈Finset.Icc 1 n) :
        k i*e (n-i) ≤ K*C*Q^n*(B/Q)^i := by
      obtain ⟨hi1,hin⟩:=Finset.mem_Icc.mp hi
      have hp : B^i*Q^(n-i)=Q^n*(B/Q)^i := by
        rw[div_pow,←mul_div_assoc]
        apply (eq_div_iff (pow_ne_zero i hQ.ne')).mpr
        calc
          _=B^i*(Q^(n-i)*Q^i):=by ring
          _=B^i*Q^n:=by rw[←pow_add,Nat.sub_add_cancel hin]
          _=_:=by ring
      calc
        _ ≤ k i*(C*Q^(n-i)):=mul_le_mul_of_nonneg_left (ih (n-i) (by omega)) (hk0 i)
        _ ≤ (K*B^i)*(C*Q^(n-i)):=mul_le_mul_of_nonneg_right (hkb i hi1) (by positivity)
        _=K*C*(B^i*Q^(n-i)):=by ring
        _=_:=by rw[hp];ring
    have hsum : (∑i∈Finset.Icc 1 n,k i*e (n-i)) ≤ K*C*Q^n*(2*(B/Q)) := by
      calc
        _ ≤ ∑i∈Finset.Icc 1 n,K*C*Q^n*(B/Q)^i:=Finset.sum_le_sum hterm
        _=K*C*Q^n*(∑i∈Finset.Icc 1 n,(B/Q)^i):=(Finset.mul_sum _ _ _).symm
        _ ≤ _:=mul_le_mul_of_nonneg_left (sum_Icc_geom_le_two_mul (B/Q) n hratio hratio2) (by positivity)
    have hcon:2*A*K*(B/Q) ≤ 1/2:=by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      have heq : (2*A*K*(B/Q))*2=(4*A*K*B)/Q := by ring
      rw[heq]
      exact (div_le_iff₀ hQ).mpr (by simpa only [one_mul] using hres)
    have hcpow:0 ≤ C*Q^n:=by positivity
    have hconv:A*(K*C*Q^n*(2*(B/Q))) ≤ (1/2)*(C*Q^n):=by
      convert mul_le_mul_of_nonneg_right hcon hcpow using 1 <;> ring
    have hforcing:A*(F*B^n) ≤ (1/2)*(C*Q^n):=by
      have hp:B^n ≤ Q^n:=pow_le_pow_left₀ hB.le (by linarith) n
      have h₁:=mul_le_mul_of_nonneg_left hp (mul_nonneg hA hF)
      have h₂:=mul_le_mul_of_nonneg_right hforce (pow_nonneg hQ.le n)
      nlinarith
    calc
      _ ≤ A*f n+A*(∑i∈Finset.Icc 1 n,k i*e (n-i)):=hrec n hn2
      _ ≤ A*(F*B^n)+A*(K*C*Q^n*(2*(B/Q))):=
        add_le_add (mul_le_mul_of_nonneg_left (hfb n) hA) (mul_le_mul_of_nonneg_left hsum hA)
      _ ≤ (1/2)*(C*Q^n)+(1/2)*(C*Q^n):=add_le_add hforcing hconv
      _=C*Q^n:=by ring

lemma four_stage_error_elimination (b F E C H G Tₑ Tₕ Tₘ:ℝ)
    (hb:0 ≤ b) (hF:0 ≤ F) (hTe:0 ≤ Tₑ) (hTh:0 ≤ Tₕ) (hTm:0 ≤ Tₘ)
    (he:E ≤ F+Tₑ) (hc:C ≤ F+b*E) (hh:H ≤ F+b*E+Tₕ)
    (hg:G ≤ F+b*(H+C)+Tₘ) :
    E+C+H+G ≤ (4+4*b+2*b^2)*F+(4+4*b+2*b^2)*(Tₑ+Tₕ+Tₘ) := by
  calc
    _ ≤ E+C+H+(F+b*(H+C)+Tₘ):=add_le_add le_rfl hg
    _=E+(b+1)*C+(b+1)*H+F+Tₘ:=by ring
    _ ≤ E+(b+1)*(F+b*E)+(b+1)*(F+b*E+Tₕ)+F+Tₘ:=by gcongr
    _=(1+2*b+2*b^2)*E+(3+2*b)*F+(b+1)*Tₕ+Tₘ:=by ring
    _ ≤ (1+2*b+2*b^2)*(F+Tₑ)+(3+2*b)*F+(b+1)*Tₕ+Tₘ:=by gcongr
    _ ≤ _:=by
      apply le_of_sub_nonneg
      convert (show 0 ≤ (3+2*b)*Tₑ+(3+3*b+2*b^2)*Tₕ+(3+4*b+2*b^2)*Tₘ by positivity) using 1 <;> ring
lemma linear_error_majorant_exists (e f k:ℕ → ℝ) (A F B K:ℝ)
    (hA:0 ≤ A) (hF:0 ≤ F) (hB:0<B) (hK:0 ≤ K)
    (hk0:∀i:ℕ,0 ≤ k i) (hkb:∀i:ℕ,1 ≤ i → k i ≤ K*B^i)
    (hfb:∀n:ℕ,f n ≤ F*B^n)
    (hrec:∀n:ℕ,2 ≤ n → e n ≤ A*f n+A*∑i∈Finset.Icc 1 n,k i*e (n-i)) :
    ∃C Q:ℝ,0<C ∧ 0<Q ∧ ∀n:ℕ,e n ≤ C*Q^n := by
  let Q:ℝ:=4*(A*K+1)*B
  have hQ:0<Q:=by dsimp[Q];positivity
  let C:ℝ:=2*A*F+|e 0|+|e 1|/Q+1
  have hC:0<C:=by dsimp[C];positivity
  have hAK:0 ≤ A*K:=mul_nonneg hA hK
  have hBq:2*B ≤ Q:=by dsimp[Q];nlinarith[mul_nonneg hAK hB.le]
  have hres:4*A*K*B ≤ Q:=by dsimp[Q];nlinarith
  have hforce:2*A*F ≤ C:=by
    dsimp[C]
    linarith [abs_nonneg (e 0),div_nonneg (abs_nonneg (e 1)) hQ.le]
  have h0:e 0 ≤ C:=by
    apply (le_abs_self (e 0)).trans
    dsimp[C]
    linarith [mul_nonneg hA hF,div_nonneg (abs_nonneg (e 1)) hQ.le]
  have h1:e 1 ≤ C*Q:=by
    have hpart:|e 1|/Q ≤ C:=by
      dsimp[C]
      linarith [mul_nonneg hA hF,abs_nonneg (e 0)]
    calc
      _ ≤ |e 1|:=le_abs_self _
      _=(|e 1|/Q)*Q:=(div_mul_cancel₀ _ hQ.ne').symm
      _ ≤ C*Q:=mul_le_mul_of_nonneg_right hpart hQ.le
  exact ⟨C,Q,hC,hQ,linear_error_majorant_bound e f k A F B K C Q hA hF hB hK hC.le hQ
    hBq hres hforce hk0 hkb hfb h0 h1 hrec⟩
end WP.HigherOrder
