import WPFormalization.Analysis.GammaEndpointErrors

/-! Growing-order falling-Gamma asymptotics from explicit jump and exact contour data. This theorem proves the Mellin transfer, including the low integral and inner-circle errors. Its jump and contour premises must still be constructed for the actual Painleve solution; it is not an external assertion or a completed endpoint theorem. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set
lemma gamma_contour_gevrey_transfer (z : ℕ→ℝ) (J : ℝ→ℝ) (v : ℕ→ℝ)
    (a C₀ D C₁ B₁ Cᵥ Bᵥ : ℝ) (G : ℕ)
    (ha : 0 ≤ a) (hC₀ : 0 ≤ C₀) (hD : 0 ≤ D) (hC₁ : 0 ≤ C₁)
    (hB₁ : 0 ≤ B₁) (hCᵥ : 0 ≤ Cᵥ) (hBᵥ : 0 ≤ Bᵥ)
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hv : ∀j:ℕ,|v j| ≤ Cᵥ*Bᵥ^j*(j.factorial:ℝ))
    (hjump : ∀L:ℕ,1 ≤ L→∀t∈Ioi a,
      |J t-(∑j∈Finset.range L,v j/t^j)| ≤ C₁*B₁^L*(L.factorial:ℝ)/t^L)
    (hcircle : ∀g:ℕ,G ≤ g→
      |z g-(∫t in Ioi a,Real.exp (-t)*t^(2*(g:ℝ)-1/2-1)*J t)/
        Real.Gamma (2*(g:ℝ)-1/2)| ≤ C₀*D^g/Real.Gamma (2*(g:ℝ)-1/2)) :
    ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀g:ℕ,G+2 ≤ g→∀L:ℕ,1 ≤ L→2*L ≤ g→
      |z g-(∑j∈Finset.range L,v j*Real.Gamma (2*(g:ℝ)-1/2-(j:ℝ)))/
        Real.Gamma (2*(g:ℝ)-1/2)| ≤ C*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L := by
  let B := B₁+2*(Bᵥ+a)+1
  let C := C₀*D*Real.exp D+C₁+Cᵥ+1
  have hB : 1 ≤ B := by dsimp [B];linarith
  have hB₁B : B₁ ≤ B := by dsimp [B];linarith
  have hBᵥB : 2*(Bᵥ+a) ≤ B := by dsimp [B];linarith
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,B,hC,by linarith,?_⟩
  intro g hg L hL hLg
  have hg2 : 2 ≤ g := by omega
  have hg1 : 1 ≤ g := by omega
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg2
  have hLR : 2*(L:ℝ) ≤ g := by exact_mod_cast hLg
  let ν := 2*(g:ℝ)-1/2
  let I := ∫t in Ioi a,Real.exp (-t)*t^(ν-1)*J t
  let S := ∑j∈Finset.range L,v j*Real.Gamma (ν-(j:ℝ))
  let low := ∫t in (0:ℝ)..a,Real.exp (-t)*t^(ν-1)*(∑j∈Finset.range L,v j/t^j)
  let K := C₁*B₁^L*(L.factorial:ℝ)
  have hν : 0<ν := by dsimp [ν];linarith
  have hνL : 0<ν-(L:ℝ) := by dsimp [ν];linarith
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hG : 0<Real.Gamma ν := Real.Gamma_pos_of_pos hν
  have hm := gamma_weighted_polynomial_remainder J v a ν K L ha hνL hK hJ (hjump L hL)
  change |I-S| ≤ K*Real.Gamma (ν-(L:ℝ))+|low| at hm
  have hlow := painleve_gamma_low_polynomial_bound v Cᵥ Bᵥ a hCᵥ hBᵥ ha hv g L hg1 hLg
  change |low/Real.Gamma ν| ≤ Cᵥ*(2*(Bᵥ+a))^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L at hlow
  have hnorm : |I/Real.Gamma ν-S/Real.Gamma ν| ≤
      C₁*B₁^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L+
        Cᵥ*(2*(Bᵥ+a))^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L := by
    rw [←sub_div,abs_div,abs_of_pos hG]
    calc
      _ ≤ (K*Real.Gamma (ν-(L:ℝ))+|low|)/Real.Gamma ν := div_le_div_of_nonneg_right hm hG.le
      _ = K*(Real.Gamma (ν-(L:ℝ))/Real.Gamma ν)+|low/Real.Gamma ν| := by
        rw [abs_div,abs_of_pos hG]
        ring
      _ ≤ K*(g:ℝ)⁻¹^L+Cᵥ*(2*(Bᵥ+a))^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L :=
        add_le_add (mul_le_mul_of_nonneg_left (gamma_painleve_falling_ratio_bound g L hg1 hLg) hK) hlow
      _ = _ := rfl
  have hcircle' : |z g-I/Real.Gamma ν| ≤ (C₀*D*Real.exp D)*(g:ℝ)⁻¹^L := by
    calc
      _ ≤ C₀*D^g/Real.Gamma ν := hcircle g (by omega)
      _ = C₀*(D^g/Real.Gamma ν) := by ring
      _ ≤ C₀*(D*Real.exp D*(g:ℝ)⁻¹^L) :=
        mul_le_mul_of_nonneg_left (gamma_painleve_inner_circle_bound D hD g L hg2 hLg) hC₀
      _ = _ := by ring
  have hfact : (1:ℝ) ≤ L.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos L)
  have hone : (1:ℝ) ≤ B^L*(L.factorial:ℝ) := by
    have hp : (1:ℝ) ≤ B^L := one_le_pow₀ hB
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hfact)]
  have h0 : (C₀*D*Real.exp D)*(g:ℝ)⁻¹^L ≤
      (C₀*D*Real.exp D)*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L := by
    have he := mul_le_mul_of_nonneg_left hone (show 0≤C₀*D*Real.exp D by positivity)
    have he' := mul_le_mul_of_nonneg_right he (show 0≤(g:ℝ)⁻¹^L by positivity)
    convert he' using 1 <;> ring
  have h1 : C₁*B₁^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L ≤ C₁*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L := by
    gcongr
  have h2 : Cᵥ*(2*(Bᵥ+a))^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L ≤ Cᵥ*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L := by
    gcongr
  change |z g-S/Real.Gamma ν| ≤ _
  calc
    _ ≤ |z g-I/Real.Gamma ν|+|I/Real.Gamma ν-S/Real.Gamma ν| := abs_sub_le _ _ _
    _ ≤ (C₀*D*Real.exp D)*(g:ℝ)⁻¹^L+
      (C₁*B₁^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L+Cᵥ*(2*(Bᵥ+a))^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L) := add_le_add hcircle' hnorm
    _ ≤ (C₀*D*Real.exp D)*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L+
      (C₁*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L+Cᵥ*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L) := add_le_add h0 (add_le_add h1 h2)
    _ = (C₀*D*Real.exp D+C₁+Cᵥ)*B^L*(L.factorial:ℝ)*(g:ℝ)⁻¹^L := by ring
    _ ≤ _ := by
      have hc : C₀*D*Real.exp D+C₁+Cᵥ ≤ C := by dsimp [C];linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (pow_nonneg (by linarith : 0≤B) L))
        (Nat.cast_nonneg _)) (by positivity)
end WP.Analysis
