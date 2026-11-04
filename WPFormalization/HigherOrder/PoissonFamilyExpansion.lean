import WPFormalization.HigherOrder.PoissonFamilyFiniteAlgebra
noncomputable section
namespace WP.HigherOrder
open Set
lemma poissonFamilyOperator_uniform_expansion (f:ℕ→ℂ × ℂ → ℂ) (R A B:ℝ)
    (hR:0<R) (hA:0<A) (hB:0<B)
    (hfa:∀s,AnalyticOnNhd ℂ (f s) (Metric.ball 0 R))
    (hfb:∀s v,v∈Metric.ball (0:ℂ × ℂ) R→‖f s v‖≤A*B^s*(s.factorial:ℝ)^2):
    ∃ν₀ C D:ℝ,0<ν₀∧ν₀<R∧0<C∧0<D∧∀(h:ℝ)(k K J:ℕ),
      0<h→(k:ℝ)/h≤ν₀→(K:ℝ)≤h/2→K≤J→2*B*((J:ℝ)+1)^2≤h→
      ‖poissonFamilyOperator f J h k-
        ∑n∈Finset.range (K+1),(h:ℂ)⁻¹^n*poissonFamilyCoefficient f n (((k:ℝ)/h:ℝ):ℂ)‖≤
        C*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
  obtain ⟨ν₀,E,hν₀,hνR,hE,hall⟩:=poisson_central_expansion_uniform_homogeneous R hR
  have hs(s:ℕ):=(hall (f s) (A*B^s*(s.factorial:ℝ)^2) (by positivity) (hfa s) (hfb s))
  let D:ℝ:=2*max B E
  have hD:0<D:=by dsimp[D];positivity
  have hBD:B≤D:=by dsimp[D];have hm:=le_max_left B E;linarith
  refine ⟨ν₀,A*(1+2*E),D,hν₀,hνR,by positivity,hD,?_⟩
  intro h k K J hh hν hK hKJ hw
  let ν:ℂ:=(((k:ℝ)/h:ℝ):ℂ)
  let a:ℂ:=(h:ℂ)⁻¹
  have hνn:‖ν‖≤ν₀:=by
    dsimp[ν]
    rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hν
  have hp:(0,ν)∈Metric.ball (0:ℂ × ℂ) R:=by
    rw[Metric.mem_ball,dist_zero_right,Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg ν)]
    exact hνn.trans_lt hνR
  have haf(s:ℕ):AnalyticAt ℂ (fun u:ℂ=>f s (u,ν)) 0:=
    (hfa s (0,ν) hp).comp (f:=fun u:ℂ=>(u,ν)) (analyticAt_id.prod analyticAt_const)
  let e:ℕ→ℂ:=fun s=>a^s*(poissonCoefficientOperator h k (fun u=>f s (u,ν))-
    ∑i∈Finset.range (K-s+1),a^i*poissonCentralAmplitude (f s) i ν)
  have he(s:ℕ) (hsk:s≤K):‖e s‖≤A*B^s*(s.factorial:ℝ)^2*
      E^(K-s+1)*((K-s+1).factorial:ℝ)/h^(K+1):=by
    have hi:((K-s:ℕ):ℝ)≤h/2:=(by exact_mod_cast Nat.sub_le K s : ((K-s:ℕ):ℝ)≤(K:ℝ)).trans hK
    have ht:‖poissonCoefficientOperator h k (fun u=>f s (u,ν))-
        ∑i∈Finset.range (K-s+1),a^i*poissonCentralAmplitude (f s) i ν‖≤
        A*B^s*(s.factorial:ℝ)^2*E^(K-s+1)*((K-s+1).factorial:ℝ)/h^(K-s+1):=by
      have ht':=(hs s).1 h k (K-s) hh hν hi
      have hsum:(∑i∈Finset.range (K-s+1),a^i*poissonCentralAmplitude (f s) i ν)=
          ∑i∈Finset.range (K-s+1),poissonCentralAmplitude (f s) i ν/(h:ℂ)^i:=by
        apply Finset.sum_congr rfl
        intro i hi
        simp only[a,inv_pow,div_eq_mul_inv,mul_comm]
      rw[hsum]
      exact ht'
    dsimp only[e]
    rw[norm_mul,norm_pow,norm_inv,Complex.norm_of_nonneg hh.le]
    apply (mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq
    rw[show h^(K+1)=h^s*h^(K-s+1) by rw[←pow_add,show s+(K-s+1)=K+1 by omega]]
    simp only[inv_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  have hlow:‖poissonFamilyOperator f K h k-
      ∑n∈Finset.range (K+1),a^n*poissonFamilyCoefficient f n ν‖≤
      A*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
    rw[poissonFamilyRemainder_exact f K h k (fun s hs=>haf s)]
    exact Analysis.poisson_low_diagonal_errors e A B E h hA hB hE hh K he
  let tail:ℂ:=∑i∈Finset.range (J-K),a^(K+1+i)*poissonCoefficientOperator h k (fun u=>f (K+1+i) (u,ν))
  have htail:‖tail‖≤2*A*E*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
    by_cases hkj:K=J
    · subst J
      simp only[tail,Nat.sub_self,Finset.sum_range_zero,norm_zero]
      positivity
    · have hNJ:K+1≤J:=by omega
      have hterm(i:ℕ):‖a^(K+1+i)*poissonCoefficientOperator h k (fun u=>f (K+1+i) (u,ν))‖≤
          A*E*(B^(K+1+i)*((K+1+i).factorial:ℝ)^2/h^(K+1+i)):=by
        rw[norm_mul,norm_pow,norm_inv,Complex.norm_of_nonneg hh.le]
        apply (mul_le_mul_of_nonneg_left ((hs (K+1+i)).2.2.2 h k hh hν) (by positivity)).trans_eq
        simp only[inv_pow,div_eq_mul_inv]
        ring
      have htailSum:∑i∈Finset.range (J-K),B^(K+1+i)*((K+1+i).factorial:ℝ)^2/h^(K+1+i)≤
          2*(B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)):=by
        have ht:=Analysis.gevreyTwo_inverse_power_tail B h hB hh (K+1) J hNJ hw
        simpa only[show J-(K+1)+1=J-K by omega] using ht
      calc
        _≤∑i∈Finset.range (J-K),‖a^(K+1+i)*poissonCoefficientOperator h k (fun u=>f (K+1+i) (u,ν))‖:=norm_sum_le _ _
        _≤∑i∈Finset.range (J-K),A*E*(B^(K+1+i)*((K+1+i).factorial:ℝ)^2/h^(K+1+i)):=Finset.sum_le_sum (fun i hi=>hterm i)
        _=A*E*(∑i∈Finset.range (J-K),B^(K+1+i)*((K+1+i).factorial:ℝ)^2/h^(K+1+i)):=(Finset.mul_sum _ _ _).symm
        _≤A*E*(2*(B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))):=mul_le_mul_of_nonneg_left htailSum (by positivity)
        _=_:=by ring
  have htailD:‖tail‖≤2*A*E*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
    apply htail.trans
    gcongr
  have hfull:poissonFamilyOperator f J h k-
      ∑n∈Finset.range (K+1),a^n*poissonFamilyCoefficient f n ν=
      (poissonFamilyOperator f K h k-
        ∑n∈Finset.range (K+1),a^n*poissonFamilyCoefficient f n ν)+tail:=by
    rw[poissonFamilyOperator_tail f J K hKJ h k (fun s hs=>haf s)]
    dsimp[tail]
    ring
  change ‖poissonFamilyOperator f J h k-∑n∈Finset.range (K+1),a^n*poissonFamilyCoefficient f n ν‖≤_
  rw[hfull]
  calc
    _≤‖poissonFamilyOperator f K h k-∑n∈Finset.range (K+1),a^n*poissonFamilyCoefficient f n ν‖+‖tail‖:=norm_add_le _ _
    _≤A*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+2*A*E*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=add_le_add hlow htailD
    _=_:=by ring
end WP.HigherOrder
