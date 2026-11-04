import WPFormalization.HigherOrder.PoissonRetainedTail
noncomputable section
namespace WP.HigherOrder
open scoped Topology
lemma poissonCentralPolynomial_coeff_zero_high (m a : ℕ) (ha : m < 2*a) :
    (poissonCentralPolynomial m).coeff a=0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((poissonCentralPolynomial_natDegree m).trans_lt (by omega))

lemma poissonCentralPolynomial_eval_inverse_orders (h : ℝ) (_hh : h≠0) (k m : ℕ) :
    (((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ)/(h:ℂ)^m=
      ∑j∈Finset.range (m+1),((poissonCentralPolynomial m).coeff (m-j):ℂ)*
        ((k:ℂ)/(h:ℂ))^(m-j)/(h:ℂ)^j := by
  have hd : (poissonCentralPolynomial m).natDegree < m+1 :=
    (poissonCentralPolynomial_natDegree m).trans_lt (by omega)
  rw [Polynomial.eval_eq_sum_range' hd]
  push_cast
  rw [Finset.sum_div]
  rw [←Finset.sum_range_reflect (fun a=>((poissonCentralPolynomial m).coeff a:ℂ)*(k:ℂ)^a/(h:ℂ)^m) (m+1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by have ht:=Finset.mem_range.mp hj;omega
  simp only [Nat.add_sub_cancel_right]
  have hp : (h:ℂ)^m=(h:ℂ)^(m-j)*(h:ℂ)^j := by rw [←pow_add,Nat.sub_add_cancel hjm]
  rw [hp,div_pow]
  field_simp

def poissonCentralFunctional (c : ℕ → ℂ) (j : ℕ) (ν : ℂ) : ℂ :=
  if j=0 then c 0 else ∑m∈Finset.Icc (j+1) (2*j),
    ((poissonCentralPolynomial m).coeff (m-j):ℂ)*ν^(m-j)*c m

lemma poissonCentralAmplitude_eq_functional (f : ℂ × ℂ → ℂ) (j : ℕ) (ν : ℂ) :
    poissonCentralAmplitude f j ν=
      poissonCentralFunctional (fun m=>WP.coeff (fun z=>f (ν+z,ν)) m) j ν := by
  by_cases hj : j=0
  · subst j
    simp [poissonCentralAmplitude,poissonCentralFunctional,WP.coeff]
  · simp only [poissonCentralAmplitude,poissonCentralFunctional,hj,ite_false,
      poissonCentralInverseCoefficient]

lemma poissonCentralFunctional_finite_rectangle (N j : ℕ) (hj : j < N)
    (c : ℕ → ℂ) (ν : ℂ) :
    (∑m∈Finset.range (2*N),if j ≤ m then
      c m*((poissonCentralPolynomial m).coeff (m-j):ℂ)*ν^(m-j) else 0)=
        poissonCentralFunctional c j ν := by
  by_cases hj0 : j=0
  · subst j
    rw [poissonCentralFunctional,ite_eq_left rfl,Finset.sum_eq_single 0]
    · simp
    · intro m hm hm0
      rw [ite_eq_left (Nat.zero_le m),Nat.sub_zero,
        poissonCentralPolynomial_coeff_zero_high m m (by omega)]
      simp
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  · have hsub : Finset.Icc (j+1) (2*j) ⊆ Finset.range (2*N) := by
      intro m hm
      simp only [Finset.mem_Icc,Finset.mem_range] at hm ⊢
      omega
    rw [poissonCentralFunctional,ite_eq_right hj0,←Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro m hm
      have ht:=Finset.mem_Icc.mp hm
      rw [ite_eq_left (by omega)]
      ring
    · intro m hm hnot
      by_cases hjm : j ≤ m
      · rw [ite_eq_left hjm]
        by_cases hmj : m=j
        · subst m
          rw [Nat.sub_self,poissonCentralPolynomial_constant j (by omega)]
          simp
        · have hmhi : 2*j < m := by simp only [Finset.mem_Icc,not_and_or,not_le] at hnot;omega
          rw [poissonCentralPolynomial_coeff_zero_high m (m-j) (by omega)]
          simp
      · rw [ite_eq_right hjm]

def poissonInverseTail (h : ℝ) (ν : ℂ) (c : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑d∈Finset.range N,(∑m∈Finset.range (2*N),if N+d ≤ m then
    c m*((poissonCentralPolynomial m).coeff (m-(N+d)):ℂ)*ν^(m-(N+d)) else 0)/(h:ℂ)^(N+d)

lemma poisson_finite_moments_rectangle (h : ℝ) (hh : h≠0) (k N : ℕ) (c : ℕ → ℂ) :
    (∑m∈Finset.range (2*N),c m*((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ))/(h:ℂ)^m)=
      ∑j∈Finset.range (2*N),(∑m∈Finset.range (2*N),if j ≤ m then
        c m*((poissonCentralPolynomial m).coeff (m-j):ℂ)*((k:ℂ)/(h:ℂ))^(m-j) else 0)/(h:ℂ)^j := by
  have hrow (m : ℕ) (hm : m∈Finset.range (2*N)) :
      c m*((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ))/(h:ℂ)^m=
        ∑j∈Finset.range (2*N),if j ≤ m then
          c m*((poissonCentralPolynomial m).coeff (m-j):ℂ)*((k:ℂ)/(h:ℂ))^(m-j)/(h:ℂ)^j else 0 := by
    rw [mul_div_assoc,poissonCentralPolynomial_eval_inverse_orders h hh,Finset.mul_sum]
    calc _ = ∑j∈Finset.range (m+1),if j ≤ m then
            c m*((poissonCentralPolynomial m).coeff (m-j):ℂ)*((k:ℂ)/(h:ℂ))^(m-j)/(h:ℂ)^j else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [ite_eq_left (by have ht:=Finset.mem_range.mp hj;omega)]
            ring
         _ = _ := by
            apply Finset.sum_subset
            · intro j hj
              simp only [Finset.mem_range] at hm hj ⊢
              omega
            · intro j hj hnot
              rw [ite_eq_right (by simp only [Finset.mem_range] at hnot;omega)]
  rw [Finset.sum_congr rfl hrow,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs <;> simp

lemma poisson_finite_moments_inverse_expansion (h : ℝ) (hh : h≠0) (k N : ℕ) (c : ℕ → ℂ) :
    (∑m∈Finset.range (2*N),c m*((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ))/(h:ℂ)^m)=
      (∑j∈Finset.range N,poissonCentralFunctional c j ((k:ℂ)/(h:ℂ))/(h:ℂ)^j)+
        poissonInverseTail h ((k:ℂ)/(h:ℂ)) c N := by
  rw [poisson_finite_moments_rectangle h hh]
  have he : Finset.range (2*N)=Finset.range (N+N) := by congr 1;omega
  rw [he,Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [←he,poissonCentralFunctional_finite_rectangle N j (Finset.mem_range.mp hj)]
  · rw [←he]
    rfl

lemma poissonInverseTail_norm_le (h r M : ℝ) (hh : 0 < h) (hr : 0 < r)
    (hM : 0 ≤ M) (N : ℕ) (hN : 1 ≤ N) (hNh : (N:ℝ) ≤ h)
    (ν : ℂ) (hν : ‖ν‖ ≤ 1) (c : ℕ → ℂ) (hc : ∀m,‖c m‖ ≤ M/r^m) :
    ‖poissonInverseTail h ν c N‖ ≤
      M*(16*(max 1 (2/r))^2)^N*(N.factorial:ℝ)/h^N := by
  let E : ℝ := M*(4*(max 1 (2/r))^2)^N*(N.factorial:ℝ)/h^N
  have hE : 0 ≤ E := by dsimp [E];positivity
  have he : poissonInverseTail h ν c N=∑d∈Finset.range N,∑m∈Finset.range (2*N),
      if N+d ≤ m then c m*((poissonCentralPolynomial m).coeff (m-(N+d)):ℂ)*ν^(m-(N+d))/(h:ℂ)^(N+d) else 0 := by
    unfold poissonInverseTail
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs <;>simp
  have hterm (d m : ℕ) (hm : m∈Finset.range (2*N)) :
      ‖if N+d ≤ m then c m*((poissonCentralPolynomial m).coeff (m-(N+d)):ℂ)*ν^(m-(N+d))/(h:ℂ)^(N+d) else 0‖ ≤ E := by
    split_ifs with hjm
    · have ht := poisson_retained_term_bound h r M hh hr hM N m (m-(N+d)) (by omega)
        (by have ht:=Finset.mem_range.mp hm;omega) (by omega) hNh ν (c m) hν (hc m)
      rw [show m-(m-(N+d))=N+d by omega] at ht
      exact ht
    · simpa using hE
  rw [he]
  calc _ ≤ ∑d∈Finset.range N,∑m∈Finset.range (2*N),
          ‖if N+d ≤ m then c m*((poissonCentralPolynomial m).coeff (m-(N+d)):ℂ)*ν^(m-(N+d))/(h:ℂ)^(N+d) else 0‖ := by
          apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro d hd
          exact norm_sum_le _ _
       _ ≤ ∑d∈Finset.range N,∑m∈Finset.range (2*N),E := by
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum
          intro m hm
          exact hterm d m hm
       _ = (N*(2*N):ℕ)*E := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_mul];ring
       _ ≤ (4:ℝ)^N*E := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact_mod_cast ((show N*(2*N) ≤ (2*N)*(N+1) by rw [Nat.mul_comm N (2*N)];exact Nat.mul_le_mul_left _ (Nat.le_succ N)).trans (poisson_retained_rectangle_card N hN))
       _ = _ := by
          have hp : (16*(max 1 (2/r))^2)^N=(4:ℝ)^N*(4*(max 1 (2/r))^2)^N := by rw [←mul_pow];congr 1;ring
          rw [hp]
          dsimp [E]
          ring

end WP.HigherOrder
