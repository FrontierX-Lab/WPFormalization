import WPFormalization.HigherOrder.ComplexInverseMajorant
/-! The genuine p=1 genus descent has a uniform scalar coefficient majorant.
The shift h+1 is retained, and the reciprocal is bounded by the proved
unit-inverse recursion. This is the local fourth-stage C.4 estimate. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

lemma descendGenus_one_uniform_norm_majorant (M : ℝ) (hM1 : 1≤M) (j : ℕ)
    (cusps : ℕ → Series) (next : Series) (η γ : WP.HigherOrder.Series)
    (hη : ∀n,0≤PowerSeries.coeff n η) (hγ : ∀n,0≤PowerSeries.coeff n γ)
    (hγ0 : PowerSeries.constantCoeff γ=1) (hc0 : PowerSeries.constantCoeff (cusps 1)=1)
    (hn : ∀i:ℕ,i≤j → ‖PowerSeries.coeff i next‖≤
      (scalarOrderWeight M i 2)^(2*i)*PowerSeries.coeff i η)
    (hc1 : ∀i:ℕ,i≤j → ‖PowerSeries.coeff i (cusps 1)‖≤
      (scalarOrderWeight M i 1)^(2*i)*PowerSeries.coeff i γ)
    (hc3 : ∀i:ℕ,i≤j → ‖PowerSeries.coeff i (cusps 3)‖≤
      (scalarOrderWeight M i 3)^(2*i)*PowerSeries.coeff i γ) :
    ‖PowerSeries.coeff j (descendGenus cusps next 1)‖≤
      Real.exp 6*(scalarOrderWeight M j 1)^(2*j)*
        PowerSeries.coeff j ((PowerSeries.exp ℝ)*η*γ*inverseUnitMajorant γ) := by
  let S : ℝ := scalarOrderWeight M j 1+2
  have hM0 : 0≤M := by linarith
  have hSJ : ((j+1:ℕ):ℝ)≤S := by
    have hm := mul_le_mul_of_nonneg_right hM1 (Nat.cast_nonneg (α:=ℝ) j)
    dsimp only [S,scalarOrderWeight]
    norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hm ⊢
    linarith
  have hS0 : 0≤S := (Nat.cast_nonneg (j+1)).trans hSJ
  have hW (i p : ℕ) (hi : i≤j) (hp : p≤3) : scalarOrderWeight M i p≤S := by
    have hm := mul_le_mul_of_nonneg_left (show (i:ℝ)≤j by exact_mod_cast hi) hM0
    have hpR : (p:ℝ)≤3 := by exact_mod_cast hp
    dsimp only [S,scalarOrderWeight]
    norm_num only [Nat.cast_one]
    linarith
  have hW0 (i p : ℕ) : 0 ≤ scalarOrderWeight M i p := by unfold scalarOrderWeight;positivity
  have hnext (i : ℕ) (hi : i≤j) : ‖PowerSeries.coeff i next‖≤S^(2*i)*PowerSeries.coeff i η :=
    (hn i hi).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hW0 i 2) (hW i 2 hi (by omega)) _) (hη i))
  have hcusps1 (i : ℕ) (hi : i≤j) : ‖PowerSeries.coeff i (cusps 1)‖≤S^(2*i)*PowerSeries.coeff i γ :=
    (hc1 i hi).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hW0 i 1) (hW i 1 hi (by omega)) _) (hγ i))
  have hcusps3 (i : ℕ) (hi : i≤j) : ‖PowerSeries.coeff i (cusps 3)‖≤S^(2*i)*PowerSeries.coeff i γ :=
    (hc3 i hi).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hW0 i 3) (hW i 3 hi (by omega)) _) (hγ i))
  have hshift (n : ℕ) (hnj : n≤j) : ‖PowerSeries.coeff n (complexityShift (-1) next)‖≤
      S^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*η) := by
    have hs := complex_shift_coeff_exponential_majorant (-1) S next (fun i=>PowerSeries.coeff i η) n (j+1)
      (by omega) (by norm_num) hSJ hη (fun i hi=>by simpa only [mul_comm] using hnext i (hi.trans hnj))
    have hmk : PowerSeries.mk (fun i=>PowerSeries.coeff i η)=η := by ext i;simp
    rw [hmk] at hs
    simpa only [complexityShift,shiftVariable] using hs
  have hinverse (n : ℕ) (hnj : n≤j) : ‖PowerSeries.coeff n ((cusps 1)⁻¹)‖≤
      S^(2*n)*PowerSeries.coeff n (inverseUnitMajorant γ) :=
    scaled_coeff_unit_inverse_bound (cusps 1) γ S hS0 hc0 hγ0 hγ n (fun i hi=>hcusps1 i (hi.trans hnj))
  have hEη := coeff_mul_nonneg exp_coeff_nonneg hη
  have hG := inverseUnitMajorant_nonneg γ hγ0 hγ
  have hprod := scaled_coeff_mul_bound (complexityShift (-1) next*cusps 3) ((cusps 1)⁻¹)
    ((PowerSeries.exp ℝ)*η*γ) (inverseUnitMajorant γ) S hS0 j
    (coeff_mul_nonneg hEη hγ) hG (fun n hn=>
      scaled_coeff_mul_bound _ _ ((PowerSeries.exp ℝ)*η) γ S hS0 n hEη hγ
        (fun i hi=>hshift i (hi.trans hn)) (fun i hi=>hcusps3 i (hi.trans hn))) hinverse
  have hSle : S≤(1:ℝ)+M*(j+1)+2 := by
    dsimp only [S,scalarOrderWeight]
    norm_num only [Nat.cast_one]
    nlinarith
  have hpow : S^(2*j)≤Real.exp 6*(scalarOrderWeight M j 1)^(2*j) :=
    (pow_le_pow_left₀ hS0 hSle _).trans (by
      simpa only [Nat.cast_one] using scalar_weight_succ_offset_pow M hM1 j 1 (by omega))
  have hpos := coeff_mul_nonneg (coeff_mul_nonneg hEη hγ) hG j
  change ‖PowerSeries.coeff j (complexityShift (-1) next*cusps 3*(cusps 1)⁻¹)‖≤_
  exact hprod.trans (mul_le_mul_of_nonneg_right hpow hpos)

end WP.HigherOrder.ComplexCanonical
