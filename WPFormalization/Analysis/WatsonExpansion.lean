import WPFormalization.Analysis.FiniteWatson
import Mathlib

/-! Exact scalar Laplace polynomial moments and a finite Watson remainder
bound. The local remainder and polynomial extension are both proved, with
all constants independent of the truncation order.
-/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set

lemma laplace_monomial_integrable (s ξ : ℝ) (hs : 0<s) (hξ : 0<ξ) (j : ℕ) :
    IntegrableOn (fun t:ℝ => Real.exp (-(ξ*t))*t^(s-1)*t^j) (Ioi 0) := by
  have h := (laplace_power_remainder_bound (fun t:ℝ => t^j) (Ioi 0) measurableSet_Ioi
    (by rfl) s ξ 1 j hs hξ (by norm_num)
    (by fun_prop) (by intro t ht;rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht.le _)];simp)).1
  simpa only [smul_eq_mul] using h

lemma laplace_monomial_integral (s ξ : ℝ) (hs : 0<s) (hξ : 0<ξ) (j : ℕ) :
    (∫ t in Ioi 0,Real.exp (-(ξ*t))*t^(s-1)*t^j)=
      (1/ξ)^(s+(j:ℝ))*Real.Gamma (s+(j:ℝ)) := by
  rw [←Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : 0<s+(j:ℝ)) hξ]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have hp : t^(s-1)*t^j=t^(s+(j:ℝ)-1) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ht]
    congr 1
    ring
  calc
    _ = (t^(s-1)*t^j)*Real.exp (-(ξ*t)) := by ring
    _ = _ := by rw [hp]

lemma laplace_polynomial_integrable (c : ℕ → ℂ) (L : ℕ) (s ξ : ℝ)
    (hs : 0<s) (hξ : 0<ξ) :
    IntegrableOn (fun t:ℝ => (Real.exp (-(ξ*t))*t^(s-1)) •
      (∑ j∈Finset.range L,t^j • c j)) (Ioi 0) := by
  have hi : IntegrableOn (fun t:ℝ => ∑ j∈Finset.range L,
      (Real.exp (-(ξ*t))*t^(s-1)*t^j) • c j) (Ioi 0) := by
    apply integrable_finsetSum
    intro j hj
    exact (laplace_monomial_integrable s ξ hs hξ j).smul_const (c j)
  convert hi using 1
  ext t
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_smul]

lemma laplace_polynomial_integral (c : ℕ → ℂ) (L : ℕ) (s ξ : ℝ)
    (hs : 0<s) (hξ : 0<ξ) :
    (∫ t in Ioi 0,(Real.exp (-(ξ*t))*t^(s-1)) •
      (∑ j∈Finset.range L,t^j • c j))=
      ∑ j∈Finset.range L,((1/ξ)^(s+(j:ℝ))*Real.Gamma (s+(j:ℝ))) • c j := by
  have he : (fun t:ℝ => (Real.exp (-(ξ*t))*t^(s-1)) •
      (∑ j∈Finset.range L,t^j • c j))=
      fun t:ℝ => ∑ j∈Finset.range L,(Real.exp (-(ξ*t))*t^(s-1)*t^j) • c j := by
    ext t
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_smul]
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_smul_const,laplace_monomial_integral s ξ hs hξ j]
  · intro j hj
    exact (laplace_monomial_integrable s ξ hs hξ j).smul_const (c j)

lemma normalized_laplace_polynomial_integral (c : ℕ → ℂ) (L : ℕ) (s ξ : ℝ)
    (hs : 0<s) (hξ : 0<ξ) :
    ξ^s • (∫ t in Ioi 0,(Real.exp (-(ξ*t))*t^(s-1)) •
      (∑ j∈Finset.range L,t^j • c j))=
      ∑ j∈Finset.range L,(Real.Gamma (s+(j:ℝ))/ξ^j) • c j := by
  rw [laplace_polynomial_integral c L s ξ hs hξ,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_smul]
  congr 1
  have hp : ξ^s*(1/ξ)^(s+(j:ℝ))=1/ξ^j := by
    rw [one_div,Real.inv_rpow hξ.le,Real.rpow_add hξ,Real.rpow_natCast]
    have hx : ξ^s≠0 := (Real.rpow_pos_of_pos hξ s).ne'
    field_simp
  calc
    _ = (ξ^s*(1/ξ)^(s+(j:ℝ)))*Real.Gamma (s+(j:ℝ)) := by ring
    _ = _ := by rw [hp];ring
lemma finite_watson_remainder_bound (f : ℝ → ℂ) (c : ℕ → ℂ) (L : ℕ) (s ξ r K M : ℝ)
    (hs : 0<s) (hs1 : s≤1) (hξ : 0<ξ) (hr : 0<r) (hK : 0≤K) (hM : 0≤M)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 r)))
    (hc : ∀j:ℕ,‖c j‖≤M/r^j)
    (herr : ∀t∈Ioc 0 r,‖f t-(∑j∈Finset.range L,t^j • c j)‖≤K*t^L) :
    ‖ξ^s • (∫t in Ioc 0 r,(Real.exp (-(ξ*t))*t^(s-1)) • f t)-
      (∑j∈Finset.range L,(Real.Gamma (s+(j:ℝ))/ξ^j) • c j)‖≤
        (K+M*(2/r)^L)*Real.Gamma s*(L.factorial:ℝ)/ξ^L := by
  let P : ℝ → ℂ := fun t => ∑j∈Finset.range L,t^j • c j
  let R : ℝ → ℂ := fun t => f t-P t
  have hPmeas : AEStronglyMeasurable P (volume.restrict (Ioc 0 r)) := by
    exact (by unfold P;fun_prop : Continuous P).aestronglyMeasurable
  have hRmeas : AEStronglyMeasurable R (volume.restrict (Ioc 0 r)) := hf.sub hPmeas
  have hRI := (laplace_power_remainder_bound R (Ioc 0 r) measurableSet_Ioc Ioc_subset_Ioi_self
    s ξ K L hs hξ hK hRmeas herr).1
  have hRN := normalized_laplace_remainder_factorial_bound R (Ioc 0 r) measurableSet_Ioc
    Ioc_subset_Ioi_self s ξ K L hs hs1 hξ hK hRmeas herr
  have hPF := laplace_polynomial_integrable c L s ξ hs hξ
  have hPI : IntegrableOn (fun t:ℝ => (Real.exp (-(ξ*t))*t^(s-1)) • P t) (Ioc 0 r) :=
    hPF.mono_set Ioc_subset_Ioi_self
  have hfI : IntegrableOn (fun t:ℝ => (Real.exp (-(ξ*t))*t^(s-1)) • f t) (Ioc 0 r) := by
    convert hRI.add hPI using 1
    funext t
    simp only [R,Pi.add_apply]
    rw [smul_sub]
    abel
  have heR : (∫t in Ioc 0 r,(Real.exp (-(ξ*t))*t^(s-1)) • R t)=
      (∫t in Ioc 0 r,(Real.exp (-(ξ*t))*t^(s-1)) • f t)-
      (∫t in Ioc 0 r,(Real.exp (-(ξ*t))*t^(s-1)) • P t) := by
    dsimp only [R]
    simp_rw [smul_sub]
    exact integral_sub hfI hPI
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hPF hr.le
  rw [intervalIntegral.integral_of_le hr.le] at hsplit
  have hC := normalized_laplace_polynomial_integral c L s ξ hs hξ
  have he : ξ^s • (∫t in Ioc 0 r,(Real.exp (-(ξ*t))*t^(s-1)) • f t)-
      (∑j∈Finset.range L,(Real.Gamma (s+(j:ℝ))/ξ^j) • c j)=
      ξ^s • ((∫t in Ioc 0 r,(Real.exp (-(ξ*t))*t^(s-1)) • R t)-
        (∫t in Ioi r,(Real.exp (-(ξ*t))*t^(s-1)) • P t)) := by
    rw [←hC,←smul_sub]
    congr 1
    dsimp only [P] at heR ⊢
    linear_combination -heR-hsplit
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hξ s)]
  calc
    _ ≤ ξ^s*(‖∫t in Ioc 0 r,(Real.exp (-(ξ*t))*t^(s-1)) • R t‖+
        ‖∫t in Ioi r,(Real.exp (-(ξ*t))*t^(s-1)) • P t‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ = ξ^s*‖∫t in Ioc 0 r,(Real.exp (-(ξ*t))*t^(s-1)) • R t‖+
        ξ^s*‖∫t in Ioi r,(Real.exp (-(ξ*t))*t^(s-1)) • P t‖ := by ring
    _ ≤ (K*Real.Gamma s*(L.factorial:ℝ)/ξ^L)+
        (M*(2/r)^L*Real.Gamma s*(L.factorial:ℝ)/ξ^L) :=
      add_le_add hRN (normalized_laplace_polynomial_tail_bound c M r s ξ hM hr hs hs1 hξ hc L)
    _ = _ := by ring

end WP.Analysis
