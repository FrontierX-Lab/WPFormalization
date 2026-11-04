import WPFormalization.Volumes.FixedCuspProof
import WPFormalization.External.SpecialFunctions

/-! Fixed-cusp normalization for the boundary-length consequence (7.19).
This is an elementary consequence of the already registered fixed-shift
Gamma ratio asymptotic. No conjectural Kimura formula is assumed. -/
noncomputable section
namespace WP
open Filter
open scoped Topology

def kimuraCuspLeadingScale (g n : ℕ) : ℝ :=
  Real.sqrt (2/Real.pi)*(4*Real.pi^2)^(2*g+n-3)*
    Real.Gamma (2*(g:ℝ)+n-5/2)

theorem kimuraCuspLeadingScale_pos (g n : ℕ) (hg : 2 ≤ g) :
    0 < kimuraCuspLeadingScale g n := by
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg
  have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hΓ : 0 < Real.Gamma (2*(g:ℝ)+n-5/2) :=
    Real.Gamma_pos_of_pos (by linarith)
  unfold kimuraCuspLeadingScale
  positivity

lemma fixed_cusp_leading_over_kimura_eq_gamma (g n : ℕ) (hg : 2 ≤ g) :
    fixedCuspLeadingScale g n/kimuraCuspLeadingScale g n =
      Real.Gamma (2*(g:ℝ)+((n:ℝ)-2)) /
        (Real.Gamma (2*(g:ℝ)+((n:ℝ)-5/2))*Real.rpow (2*(g:ℝ)) (1/2)) := by
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg
  have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have he : ((2*g+n-3:ℕ):ℝ)+1=2*(g:ℝ)+((n:ℝ)-2) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hΓ : Real.Gamma (2*(g:ℝ)+((n:ℝ)-5/2)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hP : (4*Real.pi^2)^(2*g+n-3) ≠ (0:ℝ) := by positivity
  have hs : Real.sqrt (Real.pi*g) ≠ 0 := by positivity
  have hr : Real.sqrt (2/Real.pi) ≠ 0 := by positivity
  have hroot : Real.sqrt (2*(g:ℝ))=
      Real.sqrt (Real.pi*g)*Real.sqrt (2/Real.pi) := by
    rw [←Real.sqrt_mul (by positivity : (0:ℝ)≤Real.pi*g)]
    congr 1
    field_simp
  unfold fixedCuspLeadingScale kimuraCuspLeadingScale
  rw [←Real.Gamma_nat_eq_factorial,he,Real.rpow_eq_pow,←Real.sqrt_eq_rpow,hroot]
  rw [show 2*(g:ℝ)+n-5/2=2*(g:ℝ)+((n:ℝ)-5/2) by ring]
  field_simp [hP,hs,hr,hΓ]

theorem fixed_cusp_leading_over_kimura_tendsto (n : ℕ) :
    Tendsto (fun g : ℕ => fixedCuspLeadingScale g n/kimuraCuspLeadingScale g n)
      atTop (𝓝 1) := by
  obtain ⟨C,x₀,hC,hx₀,herror⟩ :=
    External.gamma_ratio_error ((n:ℝ)-2) ((n:ℝ)-5/2)
  have hx : Tendsto (fun g : ℕ => 2*(g:ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun g : ℕ => C/(2*(g:ℝ))) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hx).const_mul C
  apply real_tendsto_of_abs_error _ _ 1 herr
  filter_upwards [eventually_ge_atTop (2:ℕ),hx.eventually_ge_atTop x₀] with g hg hxg
  rw [fixed_cusp_leading_over_kimura_eq_gamma g n hg]
  simpa only [show ((n:ℝ)-2)-((n:ℝ)-5/2)=(1/2:ℝ) by ring] using
    herror (2*(g:ℝ)) hxg

end WP
