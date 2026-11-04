import WPFormalization.Analysis.PainleveNativeDecay

/-! The actual Boutroux jump and the CCH lateral Laplace difference agree
with the exact GIKM action and Stokes normalization. This bridge proves the
coordinate powers and zero lateral parameters; it assumes no jump expansion
or identification of the symbolic CCH Stokes multiplier. -/
noncomputable section
namespace WP.Analysis
open Complex Set Filter
open WP.External.PainleveAnalytic

lemma native_jump_sqrt_scaling (ξ : ℝ) (hξ : 0<ξ) :
    Real.sqrt ξ*Real.rpow (HigherOrder.painleveJumpCoordinate ξ) (-1/8)=
      Real.sqrt piAction*Real.sqrt (HigherOrder.painleveJumpCoordinate ξ) := by
  have hA := HigherOrder.painleveAction_pos
  have hb : 0<ξ/piAction := div_pos hξ hA
  have hξe : ξ=piAction*(ξ/piAction) := by field_simp
  unfold HigherOrder.painleveJumpCoordinate
  simp only [Real.rpow_eq_pow]
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_mul hb.le,←Real.rpow_mul hb.le]
  calc
    _ = (piAction*(ξ/piAction))^(1/2:ℝ)*(ξ/piAction)^((4/5:ℝ)*(-1/8)) := by rw [←hξe]
    _ = piAction^(1/2:ℝ)*((ξ/piAction)^(1/2:ℝ)*(ξ/piAction)^((4/5:ℝ)*(-1/8))) := by
      rw [Real.mul_rpow hA.le hb.le]
      ring
    _ = _ := by
      rw [←Real.rpow_add hb]
      congr 2
      norm_num

lemma actualNativeH_jump_rescaling (G : GIKMData) (ξ : ℝ) (hξ : 0<ξ) :
    (Real.sqrt ξ:ℂ)*Complex.exp (ξ:ℂ)*(actualNativeH G 1 (ξ:ℂ)-actualNativeH G 0 (ξ:ℂ))=
      (-S₁*(Real.sqrt piAction:ℂ))*HigherOrder.normalizedPainleveJump G ξ := by
  let Z := HigherOrder.painleveJumpCoordinate ξ
  have hZ : 0<Z := Real.rpow_pos_of_pos (div_pos hξ HigherOrder.painleveAction_pos) _
  have hS : S₁≠0 := by
    unfold S₁
    exact mul_ne_zero (neg_ne_zero.mpr
      (Complex.ofReal_ne_zero.mpr HigherOrder.stokesAmplitude_pos.ne')) Complex.I_ne_zero
  have hzpow : (Real.rpow Z (-1/8):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ _).ne'
  have hden : -S₁*Complex.exp (-(ξ:ℂ))*(Real.rpow Z (-1/8):ℂ)≠0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hS) (Complex.exp_ne_zero _)) hzpow
  have hdu : G.u 1 (Z:ℂ)-G.u 0 (Z:ℂ)=
      (-S₁*Complex.exp (-(ξ:ℂ))*(Real.rpow Z (-1/8):ℂ))*HigherOrder.normalizedPainleveJump G ξ := by
    exact (mul_div_cancel₀ _ hden).symm
  have hdiff : actualNativeH G 1 (ξ:ℂ)-actualNativeH G 0 (ξ:ℂ)=
      (G.u 1 (Z:ℂ)-G.u 0 (Z:ℂ))/(Real.sqrt Z:ℂ) := by
    rw [actualNativeH_ofReal G 1 ξ hξ,actualNativeH_ofReal G 0 ξ hξ]
    dsimp [Z]
    ring
  have hs0 : (Real.sqrt Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hZ).ne'
  have hscale : (Real.sqrt ξ:ℂ)*(Real.rpow Z (-1/8):ℂ)/(Real.sqrt Z:ℂ)=(Real.sqrt piAction:ℂ) := by
    apply (div_eq_iff hs0).mpr
    have hp := native_jump_sqrt_scaling ξ hξ
    exact_mod_cast hp
  rw [hdiff,hdu]
  calc
    _ = (-S₁)*((Real.sqrt ξ:ℂ)*(Real.rpow Z (-1/8):ℂ)/(Real.sqrt Z:ℂ))*
        (Complex.exp (ξ:ℂ)*Complex.exp (-(ξ:ℂ)))*HigherOrder.normalizedPainleveJump G ξ := by ring
    _ = _ := by rw [hscale,←Complex.exp_add,add_neg_cancel,Complex.exp_zero,mul_one]

lemma actualPainleveJump_lateral_proportionality (G : GIKMData) (D : CCHData)
    (φ:ℝ) (hφ:0<φ) (hφπ:φ<Real.pi/2) :
    ∃ξ₀:ℝ,0<ξ₀ ∧ ∀ξ:ℝ,ξ₀≤ξ →
      (-S₁*(Real.sqrt piAction:ℂ))*HigherOrder.normalizedPainleveJump G ξ=
        (Real.rpow ξ (1/2):ℂ)*Complex.exp (ξ:ℂ)*
          (laplaceAlong D.H₀ (-φ) ξ-laplaceAlong D.H₀ φ ξ) := by
  obtain ⟨R₁,hR₁,h₁⟩ := actualNativeH_eq_lateral_sum G D Side.upper φ hφ hφπ
  obtain ⟨R₀,hR₀,h₀⟩ := actualNativeH_eq_lateral_sum G D Side.lower φ hφ hφπ
  refine ⟨max R₁ R₀,lt_of_lt_of_le hR₁ (le_max_left _ _),?_⟩
  intro ξ hξ
  have hξ₁ : R₁≤ξ := (le_max_left _ _).trans hξ
  have hξ₀ : R₀≤ξ := (le_max_right _ _).trans hξ
  have hp : 0<ξ := hR₁.trans_le hξ₁
  have hh₁ : actualNativeH G 1 (ξ:ℂ)=laplaceAlong D.H₀ (-φ) ξ := by
    simpa [sideSign] using h₁ ξ hξ₁
  have hh₀ : actualNativeH G 0 (ξ:ℂ)=laplaceAlong D.H₀ φ ξ := by
    simpa [sideSign] using h₀ ξ hξ₀
  rw [←actualNativeH_jump_rescaling G ξ hp,hh₁,hh₀,Real.sqrt_eq_rpow]
  rfl

end WP.Analysis
