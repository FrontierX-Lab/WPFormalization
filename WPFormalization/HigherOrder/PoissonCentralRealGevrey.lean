import WPFormalization.HigherOrder.PoissonAmplitudeBounds
import WPFormalization.HigherOrder.PoissonTaylorGevrey
noncomputable section
namespace WP.HigherOrder
open scoped Topology
lemma poisson_central_remainder_bound (h R M : ℝ) (hh : 0 < h) (hR : 0 < R)
    (hM : 0 ≤ M) (k N : ℕ) (hN : 1 ≤ N) (hNh : (N:ℝ) ≤ h)
    (hν : (k:ℝ)/h ≤ R/8) (hν1 : (k:ℝ)/h ≤ 1) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hb : ∀z∈Metric.closedBall (0:ℂ) R,‖f z‖ ≤ M) :
    ‖poissonCoefficientOperator h k f-
      ∑j∈Finset.range N,poissonCentralFunctional
        (fun m=>WP.coeff (fun z=>f ((k:ℂ)/(h:ℂ)+z)) m) j ((k:ℂ)/(h:ℂ))/(h:ℂ)^j‖ ≤
      M*((Real.exp 1*Real.sqrt (Real.pi^3)/Real.pi)*(4*Real.pi^2/R^2)^N+
        (16*(max 1 (4/R))^2)^N)*(N.factorial:ℝ)/h^N := by
  let ν : ℂ := (k:ℂ)/(h:ℂ)
  let c : ℕ → ℂ := fun m=>WP.coeff (fun z=>f (ν+z)) m
  let H : ℂ := ∑j∈Finset.range N,poissonCentralFunctional c j ν/(h:ℂ)^j
  let T : ℂ := poissonInverseTail h ν c N
  have hν0 : 0 ≤ (k:ℝ)/h := by positivity
  have hnorm : ‖ν‖=(k:ℝ)/h := by
    dsimp [ν]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hν0]
  have hc (m : ℕ) : ‖c m‖ ≤ M/(R/2)^m :=
    poisson_shifted_coeff_norm R M hR f hf hb ν (by rw [hnorm];linarith) m
  have htail := poissonInverseTail_norm_le h (R/2) M hh (half_pos hR) hM N hN hNh ν (by rw [hnorm];exact hν1) c hc
  have htail' : ‖T‖ ≤ M*(16*(max 1 (4/R))^2)^N*(N.factorial:ℝ)/h^N := by
    simpa only [T,show (2:ℝ)/(R/2)=4/R by ring] using htail
  have hpoly := poissonCoefficientOperator_taylor_error h R M hh hR hM k N hN hν f hf hb
  have hexp := poisson_finite_moments_inverse_expansion h hh.ne' k N c
  change (∑m∈Finset.range (2*N),c m*((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ))/(h:ℂ)^m)=H+T at hexp
  have hsum : (∑m∈Finset.range (2*N),WP.coeff (fun z=>f ((k:ℂ)/(h:ℂ)+z)) m*
      ((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ)/(h:ℂ)^m))=H+T := by
    calc _ = (∑m∈Finset.range (2*N),c m*((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ))/(h:ℂ)^m) := by
          apply Finset.sum_congr rfl
          intro m hm
          dsimp only [c,ν]
          ring
         _ = H+T := hexp
  rw [hsum] at hpoly
  have hpow : ((k:ℝ)/h)^N ≤ 1 := by simpa using pow_le_pow_left₀ hν0 hν1 N
  have hmain : ‖poissonCoefficientOperator h k f-(H+T)‖ ≤
      M*(Real.exp 1*Real.sqrt (Real.pi^3)/Real.pi)*(4*Real.pi^2/R^2)^N*(N.factorial:ℝ)/h^N := by
    calc _ ≤ (Real.exp 1*Real.sqrt (Real.pi^3)/(2*Real.pi))*(2*M)*
          (4*Real.pi^2/R^2)^N*(N.factorial:ℝ)*((k:ℝ)/h)^N/h^N := hpoly
         _ ≤ (Real.exp 1*Real.sqrt (Real.pi^3)/(2*Real.pi))*(2*M)*
          (4*Real.pi^2/R^2)^N*(N.factorial:ℝ)*1/h^N := by
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
         _ = _ := by ring
  change ‖poissonCoefficientOperator h k f-H‖ ≤ _
  calc _ = ‖(poissonCoefficientOperator h k f-(H+T))+T‖ := by congr 1;ring
       _ ≤ ‖poissonCoefficientOperator h k f-(H+T)‖+‖T‖ := norm_add_le _ _
       _ ≤ M*(Real.exp 1*Real.sqrt (Real.pi^3)/Real.pi)*(4*Real.pi^2/R^2)^N*(N.factorial:ℝ)/h^N+
          M*(16*(max 1 (4/R))^2)^N*(N.factorial:ℝ)/h^N := add_le_add hmain htail'
       _ = _ := by ring
lemma poisson_geometric_prefix_absorption (p B D : ℝ) (hp : 0 ≤ p) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀N : ℕ, 1 ≤ N → p*B^N+D^N ≤ C^N := by
  let E : ℝ := max 1 p*max 1 B+D
  have hE : 1 ≤ E := by
    have h1 := mul_le_mul (le_max_left 1 p) (le_max_left 1 B) (by norm_num : (0:ℝ)≤1) (by positivity)
    dsimp only [E]
    nlinarith
  refine ⟨2*E,by linarith,?_⟩
  intro N hN
  have hpN : p ≤ (max 1 p)^N := (le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))
  have hpb : p*B^N ≤ (max 1 p*max 1 B)^N := by
    rw [mul_pow]
    exact mul_le_mul hpN (pow_le_pow_left₀ hB (le_max_right _ _) _) (by positivity) (by positivity)
  have hpm : max 1 p*max 1 B ≤ E := by dsimp [E];linarith
  have hDm : D ≤ E := by
    dsimp [E]
    have ht : 0 ≤ max 1 p*max 1 B := by positivity
    linarith
  calc _ ≤ E^N+E^N := add_le_add (hpb.trans (pow_le_pow_left₀ (by positivity) hpm _)) (pow_le_pow_left₀ hD hDm _)
       _ = 2*E^N := by ring
       _ ≤ (2:ℝ)^N*E^N := mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num) (by omega)) (by positivity)
       _ = _ := by rw [mul_pow]

lemma poissonCentralFunctional_at_zero (c : ℕ → ℂ) (j : ℕ) (hj : 1 ≤ j) :
    poissonCentralFunctional c j 0=0 := by
  rw [poissonCentralFunctional,ite_eq_right (by omega)]
  apply Finset.sum_eq_zero
  intro m hm
  have ht := Finset.mem_Icc.mp hm
  simp [show m-j≠0 by omega]

lemma poisson_central_real_gevrey (R : ℝ) (hR : 0 < R) :
    ∃ ν₀ C : ℝ, 0 < ν₀ ∧ ν₀ < R/4 ∧ 2 ≤ C ∧
      ∀ (f : ℂ → ℂ), AnalyticOnNhd ℂ f (Metric.closedBall 0 R) →
        (∀z∈Metric.closedBall (0:ℂ) R,‖f z‖ ≤ 1) →
      ∀ (h : ℝ) (k K : ℕ), 0 < h → (k:ℝ)/h ≤ ν₀ → (K:ℝ) ≤ h/2 →
      ‖poissonCoefficientOperator h k f-
        ∑j∈Finset.range (K+1),poissonCentralFunctional
          (fun m=>WP.coeff (fun z=>f ((k:ℂ)/(h:ℂ)+z)) m) j ((k:ℂ)/(h:ℂ))/(h:ℂ)^j‖ ≤
        C^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := by
  let p : ℝ := Real.exp 1*Real.sqrt (Real.pi^3)/Real.pi
  let B : ℝ := 4*Real.pi^2/R^2
  let D : ℝ := 16*(max 1 (4/R))^2
  obtain ⟨C,hC,habs⟩ := poisson_geometric_prefix_absorption p B D (by dsimp [p];positivity)
    (by dsimp [B];positivity) (by dsimp [D];positivity)
  let ν₀ : ℝ := min (R/8) (1/2)
  have hν₀ : 0 < ν₀ := lt_min (by positivity) (by norm_num)
  have hνR : ν₀ ≤ R/8 := min_le_left _ _
  have hν1 : ν₀ ≤ 1/2 := min_le_right _ _
  refine ⟨ν₀,C,hν₀,by linarith,hC,?_⟩
  intro f hf hb h k K hh hν hK
  by_cases hk : 1 ≤ k
  · have hkp : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hh2 : 2 ≤ h := by
      have ht := (div_le_iff₀ hh).mp (hν.trans hν1)
      linarith
    have hNh : ((K+1:ℕ):ℝ) ≤ h := by
      by_cases hK0 : K=0
      · subst K
        norm_num
        linarith
      · have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
        push_cast
        linarith
    have ht := poisson_central_remainder_bound h R 1 hh hR (by norm_num) k (K+1) (by omega) hNh
      (hν.trans hνR) (by linarith) f hf hb
    have hs := habs (K+1) (by omega)
    calc _ ≤ (p*B^(K+1)+D^(K+1))*((K+1).factorial:ℝ)/h^(K+1) := by simpa only [one_mul,p,B,D] using ht
         _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs (by positivity)) (by positivity)
  · have hk0 : k=0 := by omega
    subst k
    rw [poissonCoefficientOperator_zero]
    simp only [Nat.cast_zero,zero_div]
    have he : (∑j∈Finset.range (K+1),poissonCentralFunctional
        (fun m=>WP.coeff (fun z=>f ((0:ℂ)+z)) m) j 0/(h:ℂ)^j)=f 0 := by
      rw [Finset.sum_eq_single 0]
      · simp [poissonCentralFunctional,WP.coeff]
      · intro j hj hj0
        rw [poissonCentralFunctional_at_zero _ j (by omega),zero_div]
      · simp
    rw [he,sub_self,norm_zero]
    positivity

end WP.HigherOrder
