import WPFormalization.Analysis.PoissonFiniteAlgebra
noncomputable section
namespace WP.Analysis
lemma weighted_triangle_sum (a:ℂ) (T:ℕ→ℕ→ℂ) (K:ℕ):
    (∑s∈Finset.range (K+1),a^s*(∑i∈Finset.range (K-s+1),a^i*T s i))=
      ∑n∈Finset.range (K+1),a^n*(∑s∈Finset.range (n+1),T s (n-s)):=by
  simp_rw[Finset.mul_sum]
  rw[sum_triangle_reindex]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro s hs
  rw[←mul_assoc,←pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hs))]
lemma sum_range_half_ratio_le (t:ℕ→ℝ) (N:ℕ)
    (ht:∀i,i≤N→0≤t i) (hr:∀i,i<N→t (i+1)≤t i/2):
    (∑i∈Finset.range (N+1),t i)≤2*t 0:=by
  induction N generalizing t with
  | zero=>simp only[Nat.zero_add,Finset.sum_range_one];linarith[ht 0 (by omega)]
  | succ N ih=>
    rw[Finset.sum_range_succ']
    have hs:=ih (fun i=>t (i+1)) (by intro i hi;exact ht _ (by omega))
      (by intro i hi;exact hr (i+1) (by omega))
    have hh:=hr 0 (by omega)
    dsimp at hs
    linarith
lemma gevreyTwo_inverse_power_tail (B h:ℝ) (hB:0<B) (hh:0<h) (N J:ℕ) (hNJ:N≤J)
    (hw:2*B*((J:ℝ)+1)^2≤h):
    (∑i∈Finset.range (J-N+1),B^(N+i)*((N+i).factorial:ℝ)^2/h^(N+i))≤
      2*(B^N*(N.factorial:ℝ)^2/h^N):=by
  let t:ℕ→ℝ:=fun i=>B^(N+i)*((N+i).factorial:ℝ)^2/h^(N+i)
  have ht(i:ℕ):0≤t i:=by dsimp[t];positivity
  have hr(i:ℕ) (hi:i<J-N):t (i+1)≤t i/2:=by
    have hin:N+i+1≤J+1:=by omega
    have hinc:(N:ℝ)+(i:ℝ)+1≤(J:ℝ)+1:=by exact_mod_cast hin
    have hcur:2*B*((N:ℝ)+(i:ℝ)+1)^2≤h:=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinc 2) (by positivity)).trans hw
    have hrat:B*((N:ℝ)+(i:ℝ)+1)^2/h≤1/2:=(div_le_iff₀ hh).mpr (by linarith)
    have he:t (i+1)=t i*(B*((N:ℝ)+(i:ℝ)+1)^2/h):=by
      dsimp[t]
      rw[show N+(i+1)=N+i+1 by omega,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      simp only[Nat.cast_add,pow_succ]
      field_simp <;> ring
    rw[he]
    exact (mul_le_mul_of_nonneg_left hrat (ht i)).trans_eq (by ring)
  have hs:=sum_range_half_ratio_le t (J-N) (by intro i hi;exact ht i) hr
  simpa only[t,Nat.add_zero] using hs
lemma poisson_low_diagonal_errors (e:ℕ→ℂ) (A B C h:ℝ)
    (hA:0<A) (hB:0<B) (hC:0<C) (hh:0<h) (K:ℕ)
    (he:∀s,s≤K→‖e s‖≤A*B^s*(s.factorial:ℝ)^2*
      C^(K-s+1)*((K-s+1).factorial:ℝ)/h^(K+1)):
    ‖∑s∈Finset.range (K+1),e s‖≤
      A*(2*max B C)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
  let D:ℝ:=max B C
  have hD:0<D:=hB.trans_le (le_max_left _ _)
  have hterm(s:ℕ) (hs:s∈Finset.range (K+1)):
      ‖e s‖≤A*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
    have hsk:s≤K:=Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    have hsum:s+(K-s+1)=K+1:=by omega
    have hp:B^s*C^(K-s+1)≤D^(K+1):=by
      calc
        _≤D^s*D^(K-s+1):=mul_le_mul
          (pow_le_pow_left₀ hB.le (le_max_left _ _) _) (pow_le_pow_left₀ hC.le (le_max_right _ _) _)
          (by positivity) (by positivity)
        _=D^(K+1):=by rw[←pow_add,hsum]
    have hf:(s.factorial:ℝ)^2*((K-s+1).factorial:ℝ)≤((K+1).factorial:ℝ)^2:=by
      simpa only[hsum] using factorial_mixed_le_square s (K-s+1)
    apply (he s hsk).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hm:=mul_le_mul_of_nonneg_left (mul_le_mul hp hf (by positivity) (by positivity)) hA.le
    convert! hm using 1 <;> ring
  have hcard:((K+1:ℕ):ℝ)≤(2:ℝ)^(K+1):=by exact_mod_cast (Nat.le_of_lt (K+1).lt_two_pow_self)
  calc
    _≤∑s∈Finset.range (K+1),‖e s‖:=norm_sum_le _ _
    _≤∑s∈Finset.range (K+1),A*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=Finset.sum_le_sum hterm
    _=((K+1:ℕ):ℝ)*(A*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)):=by simp
    _≤(2:ℝ)^(K+1)*(A*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)):=mul_le_mul_of_nonneg_right hcard (by positivity)
    _=_:=by rw[mul_pow];dsimp[D];ring
end WP.Analysis
