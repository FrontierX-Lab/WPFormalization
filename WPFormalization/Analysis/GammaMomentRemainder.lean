import WPFormalization.Analysis.GammaFallingBounds

/-! Exact Mellin moments and truncation-uniform Gamma-weighted remainder transfer for the endpoint proof. The jump remainder is an explicit input to these analytic lemmas, not an external assertion about the actual Painleve jump. The finite-cutoff formula retains the low integral explicitly. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set
lemma gamma_weighted_remainder_bound (R : ℝ→ℝ) (a ν K : ℝ) (L : ℕ)
    (ha : 0 ≤ a) (hν : 0 < ν-(L:ℝ)) (hK : 0 ≤ K)
    (hR : AEStronglyMeasurable R (volume.restrict (Ioi a)))
    (hbound : ∀ t∈Ioi a, |R t| ≤ K/t^L) :
    IntegrableOn (fun t => Real.exp (-t)*t^(ν-1)*R t) (Ioi a) ∧
      |∫ t in Ioi a,Real.exp (-t)*t^(ν-1)*R t| ≤ K*Real.Gamma (ν-(L:ℝ)) := by
  have hsub : Ioi a ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi ha
  have hg : IntegrableOn (fun t => Real.exp (-t)*t^(ν-(L:ℝ)-1)) (Ioi a) :=
    (Real.GammaIntegral_convergent hν).mono_set hsub
  have hmajor : IntegrableOn (fun t => K*(Real.exp (-t)*t^(ν-(L:ℝ)-1))) (Ioi a) := hg.const_mul K
  have hpoint (t : ℝ) (ht : t∈Ioi a) :
      ‖Real.exp (-t)*t^(ν-1)*R t‖ ≤ K*(Real.exp (-t)*t^(ν-(L:ℝ)-1)) := by
    have ht0 : 0<t := lt_of_le_of_lt ha ht
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0 ≤ Real.exp (-t)*t^(ν-1))]
    calc
      _ ≤ (Real.exp (-t)*t^(ν-1))*(K/t^L) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (by positivity)
      _ = _ := by
        rw [show ν-(L:ℝ)-1=(ν-1)-(L:ℝ) by ring,Real.rpow_sub ht0 (ν-1) (L:ℝ),Real.rpow_natCast]
        ring
  have hmeas : AEStronglyMeasurable (fun t => Real.exp (-t)*t^(ν-1)*R t)
      (volume.restrict (Ioi a)) := by
    apply AEStronglyMeasurable.mul _ hR
    exact (by fun_prop : Measurable (fun t:ℝ => Real.exp (-t)*t^(ν-1))).aestronglyMeasurable
  have hint := hmajor.mono' hmeas (ae_restrict_of_forall_mem measurableSet_Ioi hpoint)
  refine ⟨hint,?_⟩
  calc
    _ ≤ ∫ t in Ioi a,‖Real.exp (-t)*t^(ν-1)*R t‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (f:=fun t => Real.exp (-t)*t^(ν-1)*R t) (μ:=volume.restrict (Ioi a))
    _ ≤ ∫ t in Ioi a,K*(Real.exp (-t)*t^(ν-(L:ℝ)-1)) :=
      integral_mono_ae hint.norm hmajor (ae_restrict_of_forall_mem measurableSet_Ioi hpoint)
    _ = K*(∫ t in Ioi a,Real.exp (-t)*t^(ν-(L:ℝ)-1)) := integral_const_mul _ _
    _ ≤ K*(∫ t in Ioi (0:ℝ),Real.exp (-t)*t^(ν-(L:ℝ)-1)) := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply setIntegral_mono_set (Real.GammaIntegral_convergent hν)
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have ht0 : 0 ≤ t := le_of_lt ht
        positivity
      · exact Filter.Eventually.of_forall hsub
    _ = _ := by rw [←Real.Gamma_eq_integral hν]
lemma painleve_gamma_weighted_remainder_bound (R : ℝ→ℝ) (a C B : ℝ) (g L : ℕ)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hB : 0 ≤ B) (hg : 1 ≤ g) (hL : 2*L ≤ g)
    (hR : AEStronglyMeasurable R (volume.restrict (Ioi a)))
    (hbound : ∀ t∈Ioi a, |R t| ≤ C*B^L*(L.factorial:ℝ)/t^L) :
    |(∫ t in Ioi a,Real.exp (-t)*t^(2*(g:ℝ)-1/2-1)*R t)/
        Real.Gamma (2*(g:ℝ)-1/2)| ≤ C*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L := by
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hLR : 2*(L:ℝ) ≤ g := by exact_mod_cast hL
  have hν : 0 < 2*(g:ℝ)-1/2-(L:ℝ) := by linarith
  have hν0 : 0 < 2*(g:ℝ)-1/2 := by linarith
  have hK : 0 ≤ C*B^L*(L.factorial:ℝ) := by positivity
  have hb := (gamma_weighted_remainder_bound R a (2*(g:ℝ)-1/2)
    (C*B^L*(L.factorial:ℝ)) L ha hν hK hR hbound).2
  rw [abs_div,abs_of_pos (Real.Gamma_pos_of_pos hν0)]
  calc
    _ ≤ (C*B^L*(L.factorial:ℝ)*Real.Gamma (2*(g:ℝ)-1/2-(L:ℝ)))/
      Real.Gamma (2*(g:ℝ)-1/2) :=
      div_le_div_of_nonneg_right hb (Real.Gamma_pos_of_pos hν0).le
    _ = (C*B^L*(L.factorial:ℝ))*(Real.Gamma (2*(g:ℝ)-1/2-(L:ℝ))/
      Real.Gamma (2*(g:ℝ)-1/2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (gamma_painleve_falling_ratio_bound g L hg hL) hK

lemma gamma_weighted_monomial_integrable (ν : ℝ) (j : ℕ) (hν : 0 < ν-(j:ℝ)) :
    IntegrableOn (fun t:ℝ => Real.exp (-t)*t^(ν-1)/t^j) (Ioi 0) := by
  apply (Real.GammaIntegral_convergent hν).congr
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show ν-(j:ℝ)-1=(ν-1)-(j:ℝ) by ring,
    Real.rpow_sub ht (ν-1) (j:ℝ),Real.rpow_natCast]
  ring
lemma gamma_weighted_monomial_integral (ν : ℝ) (j : ℕ) (hν : 0 < ν-(j:ℝ)) :
    (∫ t:ℝ in Ioi 0,Real.exp (-t)*t^(ν-1)/t^j)=Real.Gamma (ν-(j:ℝ)) := by
  rw [Real.Gamma_eq_integral hν]
  apply integral_congr_ae
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show ν-(j:ℝ)-1=(ν-1)-(j:ℝ) by ring,
    Real.rpow_sub ht (ν-1) (j:ℝ),Real.rpow_natCast]
  ring
lemma gamma_weighted_polynomial_integral (ν : ℝ) (v : ℕ→ℝ) (L : ℕ)
    (hν : 0 < ν-(L:ℝ)) :
    (∫ t:ℝ in Ioi 0,Real.exp (-t)*t^(ν-1)*(∑j∈Finset.range L,v j/t^j))=
      ∑j∈Finset.range L,v j*Real.Gamma (ν-(j:ℝ)) := by
  have hjν (j : ℕ) (hj : j∈Finset.range L) : 0 < ν-(j:ℝ) := by
    have hjL : (j:ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hj).le
    linarith
  have heq : (fun t:ℝ => Real.exp (-t)*t^(ν-1)*(∑j∈Finset.range L,v j/t^j))=
      fun t:ℝ => ∑j∈Finset.range L,v j*(Real.exp (-t)*t^(ν-1)/t^j) := by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq,integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul,gamma_weighted_monomial_integral ν j (hjν j hj)]
  · intro j hj
    exact (gamma_weighted_monomial_integrable ν j (hjν j hj)).const_mul (v j)

lemma gamma_weighted_polynomial_integrable (ν : ℝ) (v : ℕ→ℝ) (L : ℕ)
    (hν : 0 < ν-(L:ℝ)) :
    IntegrableOn (fun t:ℝ => Real.exp (-t)*t^(ν-1)*(∑j∈Finset.range L,v j/t^j)) (Ioi 0) := by
  have hjν (j : ℕ) (hj : j∈Finset.range L) : 0 < ν-(j:ℝ) := by
    have hjL : (j:ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hj).le
    linarith
  have hi : IntegrableOn (fun t:ℝ => ∑j∈Finset.range L,v j*(Real.exp (-t)*t^(ν-1)/t^j)) (Ioi 0) := by
    apply integrable_finset_sum
    intro j hj
    exact (gamma_weighted_monomial_integrable ν j (hjν j hj)).const_mul (v j)
  convert hi using 1
  funext t
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring
lemma gamma_weighted_polynomial_remainder (J : ℝ→ℝ) (v : ℕ→ℝ)
    (a ν K : ℝ) (L : ℕ) (ha : 0 ≤ a) (hν : 0 < ν-(L:ℝ)) (hK : 0 ≤ K)
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hbound : ∀ t∈Ioi a,|J t-(∑j∈Finset.range L,v j/t^j)| ≤ K/t^L) :
    |(∫ t in Ioi a,Real.exp (-t)*t^(ν-1)*J t)-
        (∑j∈Finset.range L,v j*Real.Gamma (ν-(j:ℝ)))| ≤
      K*Real.Gamma (ν-(L:ℝ))+
        |∫ t in (0:ℝ)..a,Real.exp (-t)*t^(ν-1)*(∑j∈Finset.range L,v j/t^j)| := by
  let Q : ℝ→ℝ := fun t => ∑j∈Finset.range L,v j/t^j
  have hQ : AEStronglyMeasurable Q (volume.restrict (Ioi a)) := by
    apply Measurable.aestronglyMeasurable
    dsimp [Q]
    fun_prop
  obtain ⟨hR,hb⟩ := gamma_weighted_remainder_bound (fun t => J t-Q t) a ν K L
    ha hν hK (hJ.sub hQ) hbound
  have hPf := gamma_weighted_polynomial_integrable ν v L hν
  have hP : IntegrableOn (fun t:ℝ => Real.exp (-t)*t^(ν-1)*Q t) (Ioi a) :=
    hPf.mono_set (Ioi_subset_Ioi ha)
  have hJi : IntegrableOn (fun t:ℝ => Real.exp (-t)*t^(ν-1)*J t) (Ioi a) := by
    convert hR.add hP using 1
    funext t
    change Real.exp (-t)*t^(ν-1)*J t = Real.exp (-t)*t^(ν-1)*(J t-Q t)+Real.exp (-t)*t^(ν-1)*Q t
    ring
  have heq : (∫ t in Ioi a,Real.exp (-t)*t^(ν-1)*(J t-Q t))=
      (∫ t in Ioi a,Real.exp (-t)*t^(ν-1)*J t)-
        (∫ t in Ioi a,Real.exp (-t)*t^(ν-1)*Q t) := by
    simp_rw [mul_sub]
    exact integral_sub hJi hP
  have hs := intervalIntegral.integral_Ioi_sub_Ioi hPf ha
  rw [gamma_weighted_polynomial_integral ν v L hν] at hs
  rw [heq] at hb
  calc
    _ = |((∫ t in Ioi a,Real.exp (-t)*t^(ν-1)*J t)-
        (∫ t in Ioi a,Real.exp (-t)*t^(ν-1)*Q t))-
        (∫ t in (0:ℝ)..a,Real.exp (-t)*t^(ν-1)*Q t)| := by congr 1;dsimp [Q] at *;linarith
    _ ≤ |(∫ t in Ioi a,Real.exp (-t)*t^(ν-1)*J t)-
        (∫ t in Ioi a,Real.exp (-t)*t^(ν-1)*Q t)|+
        |∫ t in (0:ℝ)..a,Real.exp (-t)*t^(ν-1)*Q t| := abs_sub _ _
    _ ≤ _ := add_le_add hb le_rfl

end WP.Analysis
