import WPFormalization.Critical.CutCuspSeries
import WPFormalization.Critical.GammaShift

/-! Genuine uniform estimates for the reduced finite sum in Appendix G.1.
The coefficients are those of the actual unstable-component allocation
series. This module proves the numerical exponent and the marked-leaf gain;
it does not identify a geometric expected cut count with this expression. -/

noncomputable section
namespace WP.Critical
open Finset

/-- The exact remaining cusp sum in Appendix G after stable allocation. -/
def cutGammaWeightedSum (f : PowerSeries ℝ) (u n h : ℕ) : ℝ :=
  ∑m∈range (n+1),PowerSeries.coeff m f*(n.descFactorial m:ℝ)*
    (Real.Gamma ((h:ℝ)+(u:ℝ)-(m:ℝ))/Real.Gamma h)

lemma cutGammaWeightedSum_bound (u : ℕ) (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀≤h →
      (n:ℝ)≤A*Real.sqrt h → ∀f:PowerSeries ℝ,(∀m,0≤PowerSeries.coeff m f) →
      cutGammaWeightedSum f u n h ≤ C*(h:ℝ)^u*cutCoefficientMass n f ((n:ℝ)/h) := by
  obtain ⟨C,hC,H₀,hbound⟩ := gammaShift_uniform u A hA
  refine ⟨C,hC,max H₀ 1,?_⟩
  intro h n hh hn f hf
  have hp : 0<(h:ℝ) := by exact_mod_cast (by omega:0<h)
  have hterm (m:ℕ) (hm:m∈range (n+1)) :
      PowerSeries.coeff m f*(n.descFactorial m:ℝ)*
          (Real.Gamma ((h:ℝ)+(u:ℝ)-(m:ℝ))/Real.Gamma h) ≤
        C*(h:ℝ)^u*(PowerSeries.coeff m f*((n:ℝ)/h)^m) := by
    have hmn : m≤n := by have:=mem_range.mp hm;omega
    have hshift := hbound h n m (by omega) hmn hn
    have hfall : (n.descFactorial m:ℝ)≤(n:ℝ)^m := by
      exact_mod_cast Nat.descFactorial_le_pow n m
    calc
      _ ≤ PowerSeries.coeff m f*(n.descFactorial m:ℝ)*
          (C*(h:ℝ)^((u:ℝ)-(m:ℝ))) :=
        mul_le_mul_of_nonneg_left hshift (mul_nonneg (hf m) (Nat.cast_nonneg _))
      _ ≤ PowerSeries.coeff m f*(n:ℝ)^m*(C*(h:ℝ)^((u:ℝ)-(m:ℝ))) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfall (hf m)) (by positivity)
      _ = _ := by
        rw [Real.rpow_sub hp,Real.rpow_natCast,Real.rpow_natCast,div_pow]
        ring
  unfold cutGammaWeightedSum
  calc
    _ ≤ ∑m∈range (n+1), C*(h:ℝ)^u*(PowerSeries.coeff m f*((n:ℝ)/h)^m) :=
      sum_le_sum hterm
    _ = _ := by rw [←mul_sum];rfl

lemma cutGammaCuspSum_bound (u v : ℕ) (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀≤h →
      (n:ℝ)≤A*Real.sqrt h → (n:ℝ)/h≤1/2 →
      cutGammaWeightedSum (cutCuspAllocationSeries u v) u n h ≤
        C*(h:ℝ)^u*(2*((n:ℝ)/h)^2)^u*(2*((n:ℝ)/h))^v := by
  obtain ⟨C,hC,H₀,hbound⟩ := cutGammaWeightedSum_bound u A hA
  refine ⟨C,hC,H₀,?_⟩
  intro h n hh hn hnsmall
  have hz : 0≤(n:ℝ)/h := by positivity
  have hm := cutCuspAllocation_mass_bound u v n ((n:ℝ)/h) hz hnsmall
  have hb := hbound h n hh hn (cutCuspAllocationSeries u v)
    (cutCuspAllocation_coeff_nonneg u v)
  exact hb.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hm (by positivity:0≤C*(h:ℝ)^u))

end WP.Critical
namespace WP.Critical

lemma cutStableGammaRatio_bound (u w : ℕ) (hw : 1 ≤ w) (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀ ≤ h → (n:ℝ) ≤ A*Real.sqrt h →
      Real.Gamma ((h:ℝ)-(n:ℝ)+(u:ℝ)-(w:ℝ)+1) /
        Real.Gamma ((h:ℝ)-(n:ℝ)+(u:ℝ))  ≤  C*(h:ℝ)^(1-(w:ℝ)) := by
  obtain ⟨H₀,hH₀⟩ := exists_nat_ge (1+4*A^2+4*(w:ℝ))
  refine ⟨(4:ℝ)^(w-1),by positivity,H₀,?_⟩
  intro h n hh hn
  have hH : (H₀:ℝ) ≤ h := by exact_mod_cast hh
  have hh1 : 1 ≤ (h:ℝ) := by nlinarith [sq_nonneg A,Nat.cast_nonneg (α:=ℝ) w]
  have hh4A : 4*A^2 ≤ (h:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) w]
  have hh4w : 4*(w:ℝ) ≤ h := by nlinarith [sq_nonneg A]
  have hp : 0<(h:ℝ) := by linarith
  have hsq : (n:ℝ)^2 ≤ A^2*(h:ℝ) := by
    have hs := (sq_le_sq₀ (Nat.cast_nonneg n) (by positivity:0 ≤ A*Real.sqrt h)).mpr hn
    simpa only [mul_pow,Real.sq_sqrt hp.le] using hs
  have hhalf : 2*(n:ℝ) ≤ h := by nlinarith [sq_nonneg ((h:ℝ)-2*n)]
  have hwcast : ((w-1:ℕ):ℝ)=(w:ℝ)-1 := by rw [Nat.cast_sub hw];norm_num
  have hlower : (h:ℝ)/4 ≤ ((h:ℝ)-(n:ℝ)+(u:ℝ))-((w-1:ℕ):ℝ) := by
    rw [hwcast]
    linarith [Nat.cast_nonneg (α:=ℝ) u]
  have hb := (WP.Analysis.gamma_falling_ratio_bound
    ((h:ℝ)-(n:ℝ)+(u:ℝ)) ((h:ℝ)/4) (w-1) (by positivity) hlower).2
  rw [hwcast] at hb
  have he : ((h:ℝ)-(n:ℝ)+(u:ℝ))-((w:ℝ)-1)=
      (h:ℝ)-(n:ℝ)+(u:ℝ)-(w:ℝ)+1 := by ring
  rw [he] at hb
  refine hb.trans_eq ?_
  rw [show 1-(w:ℝ)=-((w-1:ℕ):ℝ) by rw [hwcast];ring,
    Real.rpow_neg hp.le,Real.rpow_natCast,inv_div,div_pow,div_eq_mul_inv]

end WP.Critical
namespace WP.Critical

lemma cutGammaCuspSum_rate (u v : ℕ) (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      cutGammaWeightedSum (cutCuspAllocationSeries u v) u n h ≤
        C*(h:ℝ)^(-(v:ℝ)/2) := by
  obtain ⟨C,hC,H₁,hbound⟩ := cutGammaCuspSum_bound u v A hA
  obtain ⟨H₂,hH₂⟩ := exists_nat_ge (1+4*A^2)
  refine ⟨C*(2*A^2)^u*(2*A)^v,by positivity,max H₁ H₂,?_⟩
  intro h n hh hn
  have hH : (H₂:ℝ)≤h := by exact_mod_cast (show H₂≤h by omega)
  have hp : 0<(h:ℝ) := by nlinarith [sq_nonneg A]
  have hsp : 0<Real.sqrt (h:ℝ) := Real.sqrt_pos.mpr hp
  have hz : 0≤(n:ℝ)/h := by positivity
  have hzbound : (n:ℝ)/h≤A/Real.sqrt h := by
    apply (div_le_div_iff₀ hp hsp).mpr
    calc
      _ ≤ (A*Real.sqrt h)*Real.sqrt h := mul_le_mul_of_nonneg_right hn hsp.le
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt hp.le]
  have hsmall : (n:ℝ)/h≤1/2 := by
    have hsq : (n:ℝ)^2≤A^2*(h:ℝ) := by
      have hs := (sq_le_sq₀ (Nat.cast_nonneg n) (by positivity:0≤A*Real.sqrt h)).mpr hn
      simpa only [mul_pow,Real.sq_sqrt hp.le] using hs
    have hhalf : 2*(n:ℝ)≤h := by nlinarith [sq_nonneg ((h:ℝ)-2*n)]
    exact (div_le_iff₀ hp).mpr (by linarith)
  have hzsq : ((n:ℝ)/h)^2≤A^2/(h:ℝ) := by
    have hb := (sq_le_sq₀ hz (by positivity:0≤A/Real.sqrt h)).mpr hzbound
    simpa only [div_pow,Real.sq_sqrt hp.le] using hb
  have hb := hbound h n (by omega) hn hsmall
  have halg : (h:ℝ)^u*(2*(A^2/(h:ℝ)))^u=(2*A^2)^u := by
    rw [←mul_pow]
    congr 1
    field_simp
  have hroot : (Real.sqrt (h:ℝ))^v=(h:ℝ)^((v:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hp.le]
    congr 1
    ring
  calc
    _ ≤ C*(h:ℝ)^u*(2*((n:ℝ)/h)^2)^u*(2*((n:ℝ)/h))^v := hb
    _ ≤ C*(h:ℝ)^u*(2*(A^2/(h:ℝ)))^u*(2*(A/Real.sqrt h))^v := by
      gcongr
    _ = C*(2*A^2)^u*((2*A)^v/(Real.sqrt (h:ℝ))^v) := by
      rw [mul_assoc C,halg,←mul_div_assoc,div_pow]
    _ = _ := by
      rw [hroot,show -(v:ℝ)/2=-((v:ℝ)/2) by ring,Real.rpow_neg hp.le]
      ring

end WP.Critical
namespace WP.Critical

lemma cutCuspScaling_bound (u v : ℕ) (A h n : ℝ) (hA : 0<A) (hp : 0<h)
    (hn0 : 0≤n) (hn : n≤A*Real.sqrt h) :
    h^u*(2*(n/h)^2)^u*(2*(n/h))^v ≤
      (2*A^2)^u*(2*A)^v*h^(-(v:ℝ)/2) := by
  have hsp : 0<Real.sqrt h := Real.sqrt_pos.mpr hp
  have hz : 0≤n/h := by positivity
  have hzbound : n/h≤A/Real.sqrt h := by
    apply (div_le_div_iff₀ hp hsp).mpr
    calc
      _ ≤ (A*Real.sqrt h)*Real.sqrt h := mul_le_mul_of_nonneg_right hn hsp.le
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt hp.le]
  have hzsq : (n/h)^2≤A^2/h := by
    have hb := (sq_le_sq₀ hz (by positivity:0≤A/Real.sqrt h)).mpr hzbound
    simpa only [div_pow,Real.sq_sqrt hp.le] using hb
  have halg : h^u*(2*(A^2/h))^u=(2*A^2)^u := by
    rw [←mul_pow]
    congr 1
    field_simp
  have hroot : (Real.sqrt h)^v=h^((v:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hp.le]
    congr 1
    ring
  calc
    _ ≤ h^u*(2*(A^2/h))^u*(2*(A/Real.sqrt h))^v := by gcongr
    _ = (2*A^2)^u*((2*A)^v/(Real.sqrt h)^v) := by
      rw [halg,←mul_div_assoc,div_pow]
    _ = _ := by
      rw [hroot,show -(v:ℝ)/2=-((v:ℝ)/2) by ring,Real.rpow_neg hp.le]
      ring

lemma cutGammaMarkedCuspSum_rate (u v : ℕ) (hu : 1≤u) (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      cutGammaWeightedSum (cutMarkedCuspAllocationSeries u v) u n h ≤
        C*(h:ℝ)^(-((v:ℝ)+1)/2) := by
  obtain ⟨C,hC,H₁,hbound⟩ := cutGammaWeightedSum_bound u A hA
  obtain ⟨H₂,hH₂⟩ := exists_nat_ge (1+4*A^2)
  refine ⟨C*A*((2*A^2)^u*(2*A)^v),by positivity,max H₁ H₂,?_⟩
  intro h n hh hn
  have hH : (H₂:ℝ)≤h := by exact_mod_cast (show H₂≤h by omega)
  have hp : 0<(h:ℝ) := by nlinarith [sq_nonneg A]
  have hsp : 0<Real.sqrt (h:ℝ) := Real.sqrt_pos.mpr hp
  have hz : 0≤(n:ℝ)/h := by positivity
  have hzbound : (n:ℝ)/h≤A/Real.sqrt h := by
    apply (div_le_div_iff₀ hp hsp).mpr
    calc
      _ ≤ (A*Real.sqrt h)*Real.sqrt h := mul_le_mul_of_nonneg_right hn hsp.le
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt hp.le]
  have hsmall : (n:ℝ)/h≤1/2 := by
    have hsq : (n:ℝ)^2≤A^2*(h:ℝ) := by
      have hs := (sq_le_sq₀ (Nat.cast_nonneg n) (by positivity:0≤A*Real.sqrt h)).mpr hn
      simpa only [mul_pow,Real.sq_sqrt hp.le] using hs
    have hhalf : 2*(n:ℝ)≤h := by nlinarith [sq_nonneg ((h:ℝ)-2*n)]
    exact (div_le_iff₀ hp).mpr (by linarith)
  have hm := cutMarkedCuspAllocation_mass_gain u v n hu ((n:ℝ)/h) hz hsmall
  have hb := hbound h n (by omega) hn (cutMarkedCuspAllocationSeries u v)
    (cutMarkedCuspAllocation_coeff_nonneg u v)
  have hs := cutCuspScaling_bound u v A h n hA hp (Nat.cast_nonneg n) hn
  have halg : (h:ℝ)^(-(v:ℝ)/2)/Real.sqrt h=(h:ℝ)^(-((v:ℝ)+1)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_sub hp]
    congr 1
    ring
  calc
    _ ≤ C*(h:ℝ)^u*(((n:ℝ)/h)*((2*((n:ℝ)/h)^2)^u*(2*((n:ℝ)/h))^v)) :=
      hb.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = C*((n:ℝ)/h)*((h:ℝ)^u*(2*((n:ℝ)/h)^2)^u*(2*((n:ℝ)/h))^v) := by ring
    _ ≤ C*(A/Real.sqrt h)*((2*A^2)^u*(2*A)^v*(h:ℝ)^(-(v:ℝ)/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hzbound hC.le) hs (by positivity) (by positivity)
    _ = _ := by rw [←halg];ring

end WP.Critical
namespace WP.Critical
open Finset

/-- The reduced numerical sum in the proof of Lemma G.1, before the fixed
constant from stable Gamma convolution and geometric integration. -/
def cutCriticalReducedSum (f : PowerSeries ℝ) (u w n h : ℕ) : ℝ :=
  (Real.Gamma ((h:ℝ)-(n:ℝ)+(u:ℝ)-(w:ℝ)+1) /
    Real.Gamma ((h:ℝ)-(n:ℝ)+(u:ℝ))) * cutGammaWeightedSum f u n h

lemma cutGammaWeightedSum_nonneg (f : PowerSeries ℝ) (u n h : ℕ)
    (hf : ∀m,0≤PowerSeries.coeff m f) (hp : 0<(h:ℝ)) (hn : 2*(n:ℝ)≤h) :
    0≤cutGammaWeightedSum f u n h := by
  unfold cutGammaWeightedSum
  apply sum_nonneg
  intro m hm
  have hmn : (m:ℝ)≤n := by exact_mod_cast (by have:=mem_range.mp hm;omega: m≤n)
  have harg : 0<(h:ℝ)+(u:ℝ)-(m:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) u]
  exact mul_nonneg (mul_nonneg (hf m) (Nat.cast_nonneg _))
    (div_pos (Real.Gamma_pos_of_pos harg) (Real.Gamma_pos_of_pos hp)).le

lemma cutCriticalReducedSum_rate_of_weighted (f : PowerSeries ℝ) (u w : ℕ)
    (hw : 1≤w) (A : ℝ) (hA : 0<A) (δ : ℝ)
    (hf : ∀m,0≤PowerSeries.coeff m f)
    (hweighted : ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      cutGammaWeightedSum f u n h≤C*(h:ℝ)^δ) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      cutCriticalReducedSum f u w n h ≤ C*(h:ℝ)^(1-(w:ℝ)+δ) := by
  obtain ⟨C₁,hC₁,H₁,h₁⟩ := hweighted
  obtain ⟨C₂,hC₂,H₂,h₂⟩ := cutStableGammaRatio_bound u w hw A hA
  obtain ⟨H₃,hH₃⟩ := exists_nat_ge (1+4*A^2)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,max H₁ (max H₂ H₃),?_⟩
  intro h n hh hn
  have hH : (H₃:ℝ)≤h := by exact_mod_cast (show H₃≤h by omega)
  have hp : 0<(h:ℝ) := by nlinarith [sq_nonneg A]
  have hsq : (n:ℝ)^2≤A^2*(h:ℝ) := by
    have hs := (sq_le_sq₀ (Nat.cast_nonneg n) (by positivity:0≤A*Real.sqrt h)).mpr hn
    simpa only [mul_pow,Real.sq_sqrt hp.le] using hs
  have hhalf : 2*(n:ℝ)≤h := by nlinarith [sq_nonneg ((h:ℝ)-2*n)]
  have hsum := cutGammaWeightedSum_nonneg f u n h hf hp hhalf
  have hb := mul_le_mul (h₂ h n (by omega) hn) (h₁ h n (by omega) hn)
    hsum (by positivity:0≤C₂*(h:ℝ)^(1-(w:ℝ)))
  unfold cutCriticalReducedSum
  exact hb.trans_eq (by rw [Real.rpow_add hp];ring)

lemma cutCriticalReducedSum_rate (u v w : ℕ) (hw : 1≤w) (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      cutCriticalReducedSum (cutCuspAllocationSeries u v) u w n h ≤
        C*(h:ℝ)^(1-(w:ℝ)-(v:ℝ)/2) := by
  simpa only [sub_eq_add_neg,neg_div] using
    cutCriticalReducedSum_rate_of_weighted (cutCuspAllocationSeries u v) u w hw A hA
      (-(v:ℝ)/2) (cutCuspAllocation_coeff_nonneg u v) (cutGammaCuspSum_rate u v A hA)

lemma cutCriticalMarkedReducedSum_rate (u v w : ℕ) (hu : 1≤u) (hw : 1≤w)
    (A : ℝ) (hA : 0<A) :
    ∃C:ℝ,0<C ∧ ∃H₀:ℕ,∀h n:ℕ,H₀≤h → (n:ℝ)≤A*Real.sqrt h →
      cutCriticalReducedSum (cutMarkedCuspAllocationSeries u v) u w n h ≤
        C*(h:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2) := by
  simpa only [sub_eq_add_neg,neg_div] using
    cutCriticalReducedSum_rate_of_weighted (cutMarkedCuspAllocationSeries u v) u w hw A hA
      (-((v:ℝ)+1)/2) (cutMarkedCuspAllocation_coeff_nonneg u v)
      (cutGammaMarkedCuspSum_rate u v hu A hA)

end WP.Critical
