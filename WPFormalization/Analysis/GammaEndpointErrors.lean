import WPFormalization.Analysis.GammaMomentRemainder

/-! Uniform bounds for the finite low integral and inner-circle error in the endpoint Mellin formula. These estimates retain the actual finite polynomial and use only Gamma identities, monotonicity and exponential-series bounds. No Painleve jump or contour assertion is assumed here. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set
lemma inverse_polynomial_cutoff_bound (v : ℕ→ℝ) (L : ℕ) (a t : ℝ)
    (ht : 0 < t) (hta : t ≤ a) :
    |∑j∈Finset.range L,v j/t^j| ≤ (∑j∈Finset.range L,|v j| * a^(L-j))/t^L := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑j∈Finset.range L,(|v j| * a^(L-j))/t^L := by
      apply Finset.sum_le_sum
      intro j hj
      have hjL : j ≤ L := (Finset.mem_range.mp hj).le
      rw [abs_div,abs_of_nonneg (pow_nonneg ht.le _)]
      have hp : t^j*t^(L-j)=t^L := by rw [←pow_add,Nat.add_sub_of_le hjL]
      calc
        _ = (|v j| * t^(L-j))/t^L := by
          field_simp
          rw [←hp]
          ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hta _) (abs_nonneg _)) (by positivity)
    _ = _ := by rw [Finset.sum_div]
lemma factorial_polynomial_cutoff_sum_bound (v : ℕ→ℝ) (C B a : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hv : ∀j:ℕ,|v j| ≤ C*B^j*(j.factorial:ℝ)) (L : ℕ) :
    (∑j∈Finset.range L,|v j| * a^(L-j)) ≤ C*(2*(B+a))^L*(L.factorial:ℝ) := by
  have ht (j : ℕ) (hj : j∈Finset.range L) :
      |v j| * a^(L-j) ≤ C*(B+a)^L*(L.factorial:ℝ) := by
    have hjL : j ≤ L := (Finset.mem_range.mp hj).le
    have hfac : (j.factorial:ℝ) ≤ L.factorial := by exact_mod_cast Nat.factorial_le hjL
    calc
      _ ≤ (C*B^j*(j.factorial:ℝ))*a^(L-j) := mul_le_mul_of_nonneg_right (hv j) (by positivity)
      _ ≤ (C*(B+a)^j*(L.factorial:ℝ))*(B+a)^(L-j) := by
        apply mul_le_mul
        · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB (by linarith) j) hC)
            hfac (by positivity) (by positivity)
        · exact pow_le_pow_left₀ ha (by linarith) _
        · positivity
        · positivity
      _ = _ := by
        have hp : (B+a)^j*(B+a)^(L-j)=(B+a)^L := by rw [←pow_add,Nat.add_sub_of_le hjL]
        calc
          _ = C*((B+a)^j*(B+a)^(L-j))*(L.factorial:ℝ) := by ring
          _ = _ := by rw [hp]
  calc
    _ ≤ ∑j∈Finset.range L,C*(B+a)^L*(L.factorial:ℝ) := Finset.sum_le_sum ht
    _ = (L:ℝ)*(C*(B+a)^L*(L.factorial:ℝ)) := by simp
    _ ≤ (2:ℝ)^L*(C*(B+a)^L*(L.factorial:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show L ≤ (2:ℕ)^L from Nat.le_of_lt Nat.lt_two_pow_self)
    _ = _ := by rw [mul_pow];ring
lemma gamma_weighted_low_polynomial_bound (v : ℕ→ℝ) (L : ℕ) (a ν : ℝ)
    (ha : 0 ≤ a) (hν : 0 < ν-(L:ℝ)) :
    |∫ t in (0:ℝ)..a,Real.exp (-t)*t^(ν-1)*(∑j∈Finset.range L,v j/t^j)| ≤
      (∑j∈Finset.range L,|v j| * a^(L-j))*Real.Gamma (ν-(L:ℝ)) := by
  let Q : ℝ→ℝ := fun t => ∑j∈Finset.range L,v j/t^j
  let R : ℝ→ℝ := (Iic a).indicator Q
  let K : ℝ := ∑j∈Finset.range L,|v j| * a^(L-j)
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hR : AEStronglyMeasurable R (volume.restrict (Ioi (0:ℝ))) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ measurableSet_Iic
    dsimp [Q]
    fun_prop
  have hbound : ∀ t∈Ioi (0:ℝ),|R t| ≤ K/t^L := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases hta : t ≤ a
    · dsimp [R]
      rw [Set.indicator_of_mem (show t∈Iic a from hta)]
      exact inverse_polynomial_cutoff_bound v L a t ht hta
    · dsimp [R]
      rw [Set.indicator_of_notMem (show t∉Iic a from hta),abs_zero]
      positivity
  have hb := (gamma_weighted_remainder_bound R 0 ν K L (by norm_num) hν hK hR hbound).2
  have heq : (fun t:ℝ => Real.exp (-t)*t^(ν-1)*R t)=
      (Iic a).indicator (fun t:ℝ => Real.exp (-t)*t^(ν-1)*Q t) := by
    funext t
    by_cases ht : t∈Iic a <;> simp [R,ht]
  rw [heq,setIntegral_indicator measurableSet_Iic,
    show Ioi (0:ℝ)∩Iic a=Ioc 0 a by ext t;simp only [mem_inter_iff,mem_Ioi,mem_Iic,mem_Ioc]] at hb
  simpa only [intervalIntegral.integral_of_le ha] using hb
lemma painleve_gamma_low_polynomial_bound (v : ℕ→ℝ) (C B a : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hv : ∀j:ℕ,|v j| ≤ C*B^j*(j.factorial:ℝ)) (g L : ℕ)
    (hg : 1 ≤ g) (hL : 2*L ≤ g) :
    |(∫ t in (0:ℝ)..a,Real.exp (-t)*t^(2*(g:ℝ)-1/2-1)*
      (∑j∈Finset.range L,v j/t^j))/Real.Gamma (2*(g:ℝ)-1/2)| ≤
      C*(2*(B+a))^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L := by
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hLR : 2*(L:ℝ) ≤ g := by exact_mod_cast hL
  have hν : 0 < 2*(g:ℝ)-1/2-(L:ℝ) := by linarith
  have hν0 : 0 < 2*(g:ℝ)-1/2 := by linarith
  have hK : 0 ≤ C*(2*(B+a))^L*(L.factorial:ℝ) := by positivity
  have hb := gamma_weighted_low_polynomial_bound v L a (2*(g:ℝ)-1/2) ha hν
  have hc := factorial_polynomial_cutoff_sum_bound v C B a hC hB ha hv L
  have he := hb.trans (mul_le_mul_of_nonneg_right hc (Real.Gamma_pos_of_pos hν).le)
  rw [abs_div,abs_of_pos (Real.Gamma_pos_of_pos hν0)]
  calc
    _ ≤ (C*(2*(B+a))^L*(L.factorial:ℝ)*Real.Gamma (2*(g:ℝ)-1/2-(L:ℝ)))/
        Real.Gamma (2*(g:ℝ)-1/2) :=
      div_le_div_of_nonneg_right he (Real.Gamma_pos_of_pos hν0).le
    _ = (C*(2*(B+a))^L*(L.factorial:ℝ))*(Real.Gamma (2*(g:ℝ)-1/2-(L:ℝ))/
        Real.Gamma (2*(g:ℝ)-1/2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (gamma_painleve_falling_ratio_bound g L hg hL) hK

lemma gamma_painleve_inner_circle_bound (D : ℝ) (hD : 0 ≤ D) (g L : ℕ)
    (hg : 2 ≤ g) (hL : 2*L ≤ g) :
    D^g/Real.Gamma (2*(g:ℝ)-1/2) ≤ D*Real.exp D*(g:ℝ)⁻¹^L := by
  have hg1 : 1 ≤ g := by omega
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg
  have hLR : 2*(L:ℝ) ≤ g := by exact_mod_cast hL
  have hνL : (g:ℝ) ≤ 2*(g:ℝ)-1/2-(L:ℝ) := by linarith
  have hν0 : 0 < 2*(g:ℝ)-1/2 := by linarith
  have hfac : (0:ℝ) < (g-1).factorial := by exact_mod_cast Nat.factorial_pos (g-1)
  have hG : ((g-1).factorial:ℝ) ≤ Real.Gamma (2*(g:ℝ)-1/2-(L:ℝ)) := by
    have he : (g:ℝ)=((g-1:ℕ):ℝ)+1 := by exact_mod_cast (Nat.sub_add_cancel hg1).symm
    calc
      _ = Real.Gamma (g:ℝ) := by rw [he,Real.Gamma_nat_eq_factorial]
      _ ≤ _ := Real.Gamma_strictMonoOn_Ici.monotoneOn hgR (hgR.trans hνL) hνL
  have hpow : D^g ≤ D*Real.exp D*((g-1).factorial:ℝ) := by
    have he := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp D hD (g-1))
    have ht := mul_le_mul_of_nonneg_left he hD
    rw [mul_comm D (D^(g-1)),←pow_succ, Nat.sub_add_cancel hg1] at ht
    convert ht using 1 <;> ring
  have hpowG : D^g ≤ D*Real.exp D*Real.Gamma (2*(g:ℝ)-1/2-(L:ℝ)) :=
    hpow.trans (mul_le_mul_of_nonneg_left hG (by positivity))
  calc
    _ ≤ (D*Real.exp D*Real.Gamma (2*(g:ℝ)-1/2-(L:ℝ)))/Real.Gamma (2*(g:ℝ)-1/2) :=
      div_le_div_of_nonneg_right hpowG (Real.Gamma_pos_of_pos hν0).le
    _ = (D*Real.exp D)*(Real.Gamma (2*(g:ℝ)-1/2-(L:ℝ))/Real.Gamma (2*(g:ℝ)-1/2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (gamma_painleve_falling_ratio_bound g L hg1 hL) (by positivity)
end WP.Analysis
