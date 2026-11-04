import WPFormalization.Analysis.GammaFallingBounds
noncomputable section
namespace WP.Critical
open Finset

lemma gammaShift_inverse_factor (h l : ℝ) (hh : 0 < h) (hl : 0 ≤ l) (hlh : 2*l ≤ h) :
    (h-l)⁻¹ ≤ h⁻¹*Real.exp (2*l/h) := by
  have hhm : 0 < h-l := by linarith
  have ht : 0 ≤ l*(h-2*l)/h^2 := by positivity
  have he : h⁻¹*(1+2*l/h)*(h-l)=1+l*(h-2*l)/h^2 := by
    field_simp
    <;> ring
  have hbase : (h-l)⁻¹ ≤ h⁻¹*(1+2*l/h) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hhm).mpr
    rw [he]
    linarith
  apply hbase.trans
  exact mul_le_mul_of_nonneg_left (by simpa [add_comm] using Real.add_one_le_exp (2*l/h))
    (inv_nonneg.mpr hh.le)

lemma gammaShift_falling_uniform (A h : ℝ) (m : ℕ) (hA : 0 < A)
    (hh : 1 ≤ h) (hsize : 4*A^2 ≤ h) (hm : (m:ℝ) ≤ A*Real.sqrt h) :
    Real.Gamma (h-(m:ℝ))/Real.Gamma h ≤ Real.exp (2*A^2)/h^m := by
  have hp : 0 < h := by linarith
  have hm0 : 0 ≤ (m:ℝ) := by positivity
  have hsq : (m:ℝ)^2 ≤ A^2*h := by
    have hs := (sq_le_sq₀ hm0 (by positivity : 0 ≤ A*Real.sqrt h)).mpr hm
    simpa only [mul_pow,Real.sq_sqrt hp.le] using hs
  have hhalf : 2*(m:ℝ) ≤ h := by nlinarith [sq_nonneg (h-2*m)]
  have hhm : 0 < h-(m:ℝ) := by linarith
  have hb := (WP.Analysis.gamma_falling_ratio_bound h (h-(m:ℝ)) m hhm le_rfl).2
  have hf := gammaShift_inverse_factor h m hp hm0 hhalf
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (h-(m:ℝ))⁻¹) hf m
  have he : (h⁻¹*Real.exp (2*(m:ℝ)/h))^m = Real.exp (2*(m:ℝ)^2/h)/h^m := by
    rw [mul_pow,←Real.exp_nat_mul,inv_pow]
    rw [div_eq_mul_inv]
    conv_lhs => rw [mul_comm]
    congr 1
    congr 1
    ring
  have hexp : Real.exp (2*(m:ℝ)^2/h) ≤ Real.exp (2*A^2) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hsq]
  calc
    _ ≤ ((h-(m:ℝ))⁻¹)^m := hb
    _ ≤ _ := hpow
    _ = _ := he
    _ ≤ _ := div_le_div_of_nonneg_right hexp (by positivity)

end WP.Critical
namespace WP.Critical
lemma gammaShift_uniform_real (u : ℕ) (A h : ℝ) (m : ℕ) (hA : 0 < A)
    (hh : 1 ≤ h) (hsize : 4*A^2 ≤ h) (hm : (m:ℝ) ≤ A*Real.sqrt h) :
    Real.Gamma (h+(u:ℝ)-(m:ℝ))/Real.Gamma h ≤
      ((1+(u:ℝ))^u*Real.exp (2*A^2))*h^((u:ℝ)-(m:ℝ)) := by
  have hp : 0 < h := by linarith
  have hm0 : 0 ≤ (m:ℝ) := by positivity
  have hsq : (m:ℝ)^2 ≤ A^2*h := by
    have hs := (sq_le_sq₀ hm0 (by positivity : 0 ≤ A*Real.sqrt h)).mpr hm
    simpa only [mul_pow,Real.sq_sqrt hp.le] using hs
  have hhalf : 2*(m:ℝ) ≤ h := by nlinarith [sq_nonneg (h-2*m)]
  have hhm : 0 < h-(m:ℝ) := by linarith
  have hgam := WP.External.gamma_finite_product (h-(m:ℝ)) hhm u
  rw [show h-(m:ℝ)+(u:ℝ)=h+(u:ℝ)-(m:ℝ) by ring] at hgam
  have hprod : (∏ j ∈ Finset.range u, (h-(m:ℝ)+(j:ℝ))) ≤ ((1+(u:ℝ))*h)^u := by
    calc
      _ ≤ ∏ _j ∈ Finset.range u, ((1+(u:ℝ))*h) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          have hj0 : 0 ≤ (j:ℝ) := by positivity
          linarith
        · intro j hj
          have hjlt : (j:ℝ) < u := by exact_mod_cast Finset.mem_range.mp hj
          have hu : 0 ≤ (u:ℝ) := by positivity
          nlinarith
      _ = _ := by simp
  have hfall := gammaShift_falling_uniform A h m hA hh hsize hm
  have hfallpos : 0 ≤ Real.Gamma (h-(m:ℝ))/Real.Gamma h :=
    (div_pos (Real.Gamma_pos_of_pos hhm) (Real.Gamma_pos_of_pos hp)).le
  have he : Real.Gamma (h+(u:ℝ)-(m:ℝ))/Real.Gamma h =
      (∏ j ∈ Finset.range u, (h-(m:ℝ)+(j:ℝ)))*
        (Real.Gamma (h-(m:ℝ))/Real.Gamma h) := by rw [hgam]; ring
  rw [he]
  calc
    _ ≤ (((1+(u:ℝ))*h)^u)*(Real.exp (2*A^2)/h^m) :=
      mul_le_mul hprod hfall hfallpos (by positivity)
    _ = _ := by
      rw [mul_pow,Real.rpow_sub hp,Real.rpow_natCast,Real.rpow_natCast]
      ring

lemma gammaShift_uniform (u : ℕ) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℕ, ∀ h n m : ℕ, H₀ ≤ h → m ≤ n →
      (n:ℝ) ≤ A*Real.sqrt h →
      Real.Gamma ((h:ℝ)+(u:ℝ)-(m:ℝ))/Real.Gamma h ≤
        C*(h:ℝ)^((u:ℝ)-(m:ℝ)) := by
  obtain ⟨H,hH⟩ := exists_nat_ge (1+4*A^2)
  refine ⟨(1+(u:ℝ))^u*Real.exp (2*A^2),by positivity,H,?_⟩
  intro h n m hh hmn hn
  have hHh : (H:ℝ) ≤ h := by exact_mod_cast hh
  have hh1 : (1:ℝ) ≤ h := by nlinarith [sq_nonneg A]
  have hhA : 4*A^2 ≤ (h:ℝ) := by linarith
  have hmnR : (m:ℝ) ≤ n := by exact_mod_cast hmn
  exact gammaShift_uniform_real u A h m hA hh1 hhA (hmnR.trans hn)
end WP.Critical
