import WPFormalization.Analysis.PainleveBorelGevrey
import WPFormalization.Analysis.PainleveNativeJumpBridge
import WPFormalization.HigherOrder.ComplexAsymptoticUniqueness
import WPFormalization.HigherOrder.PainleveJumpFixedOrder
/-! Actual order-uniform Gevrey remainder for the canonical PI jump.
The exact native-to-lateral bridge is proved locally. Normalized raw Borel
coefficients are identified with the actual rational jump table by fixed-order
asymptotic uniqueness, including the leading multiplier normalization. No
numeric Stokes value or uniform jump estimate is an external input. -/
noncomputable section
namespace WP.HigherOrder
open WP.External.PainleveAnalytic

def jumpStokesScale : ℂ := -S₁*(Real.sqrt External.painleveAction:ℂ)
lemma jumpStokesScale_ne_zero : jumpStokesScale≠0 := by
  unfold jumpStokesScale S₁
  have hS : (External.stokesAmplitude:ℂ)≠0:=Complex.ofReal_ne_zero.mpr stokesAmplitude_pos.ne'
  have hA : (Real.sqrt External.painleveAction:ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr painleveAction_pos).ne'
  exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr hS) Complex.I_ne_zero)) hA

def borelJumpCoefficient (D:CCHData) (j:ℕ) : ℂ :=
  ((-2*Complex.I)*D.S)/jumpStokesScale*(Real.Gamma ((1/2:ℝ)+(j:ℝ)):ℂ)*
    WP.coeff (fun z:ℂ=>D.α (1+z)) j

lemma borelJumpPolynomial_scale (D:CCHData) (L:ℕ) (ξ:ℝ) :
    jumpStokesScale*(∑j∈Finset.range L,borelJumpCoefficient D j/(ξ:ℂ)^j)=
      ((-2*Complex.I)*D.S)*(∑j∈Finset.range L,
        (Real.Gamma ((1/2:ℝ)+(j:ℝ))/ξ^j) • WP.coeff (fun z:ℂ=>D.α (1+z)) j) := by
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.real_smul]
  unfold borelJumpCoefficient
  push_cast
  field_simp [jumpStokesScale_ne_zero]

lemma normalized_jump_gevrey_of_lateral (G:GIKMData) (D:CCHData)
    (hrep : ∀φ:ℝ,0<φ → φ<Real.pi/2 → ∃R:ℝ,0<R ∧ ∀ξ:ℝ,R≤ξ →
      jumpStokesScale*normalizedPainleveJump G ξ=
        ((ξ^(1/2:ℝ):ℝ):ℂ)*Complex.exp (ξ:ℂ)*
          (laplaceAlong D.H₀ (-φ) ξ-laplaceAlong D.H₀ φ ξ)) :
    ∃C B R:ℝ,0<C ∧ 0<B ∧ 0<R ∧ ∀L:ℕ,∀ξ:ℝ,R≤ξ →
      ‖normalizedPainleveJump G ξ-
        ∑j∈Finset.range L,((jumpCoefficient j:ℝ):ℂ)/(ξ:ℂ)^j‖≤
        C*B^L*(L.factorial:ℝ)/ξ^L := by
  obtain ⟨φ,C,B,R,hφ,hφπ,hC,hB,hR,he⟩:=WP.Analysis.cch_rescaled_jump_gevrey D
  obtain ⟨T,hT,hrep⟩:=hrep φ hφ hφπ
  have hnorm : 0<‖jumpStokesScale‖:=norm_pos_iff.mpr jumpStokesScale_ne_zero
  have hraw : ∀L:ℕ,∀ξ:ℝ,max R T≤ξ →
      ‖normalizedPainleveJump G ξ-∑j∈Finset.range L,borelJumpCoefficient D j/(ξ:ℂ)^j‖≤
        (C/‖jumpStokesScale‖)*B^L*(L.factorial:ℝ)/ξ^L := by
    intro L ξ hξ
    have hξR : R≤ξ:=(le_max_left _ _).trans hξ
    have hξT : T≤ξ:=(le_max_right _ _).trans hξ
    have hh:=he L ξ hξR
    rw [←hrep ξ hξT,←borelJumpPolynomial_scale,←mul_sub] at hh
    calc
      _ = ‖jumpStokesScale*(normalizedPainleveJump G ξ-
          ∑j∈Finset.range L,borelJumpCoefficient D j/(ξ:ℂ)^j)‖/‖jumpStokesScale‖ := by
        rw [norm_mul]
        field_simp [hnorm.ne']
      _ ≤ (C*B^L*(L.factorial:ℝ)/ξ^L)/‖jumpStokesScale‖ :=
        div_le_div_of_nonneg_right hh hnorm.le
      _ = _ := by ring
  have hfixed : HasComplexInversePowerExpansion (normalizedPainleveJump G)
      (fun j:ℕ=>((jumpCoefficient j:ℝ):ℂ)):=normalizedPainleveJump_fixed_order G
  have hBorel : HasComplexInversePowerExpansion (normalizedPainleveJump G) (borelJumpCoefficient D) := by
    intro K
    refine ⟨(C/‖jumpStokesScale‖)*B^(K+1)*((K+1).factorial:ℝ),max R T,
      by positivity,lt_of_lt_of_le hR (le_max_left _ _),?_⟩
    intro ξ hξ
    exact hraw (K+1) ξ hξ
  have hid := complex_inverse_power_expansion_unique _ _ _ hBorel hfixed
  refine ⟨C/‖jumpStokesScale‖,B,max R T,div_pos hC hnorm,hB,
    lt_of_lt_of_le hR (le_max_left _ _),?_⟩
  intro L ξ hξ
  simpa only [hid] using hraw L ξ hξ

/-- Uniform factorial remainder for the actual canonical GIKM jump. -/
theorem normalizedPainleveJump_gevrey (G:GIKMData) (D:CCHData) :
    ∃C B R:ℝ,0<C ∧ 0<B ∧ 0<R ∧ ∀L:ℕ,∀ξ:ℝ,R≤ξ →
      ‖normalizedPainleveJump G ξ-
        ∑j∈Finset.range L,((jumpCoefficient j:ℝ):ℂ)/(ξ:ℂ)^j‖≤
        C*B^L*(L.factorial:ℝ)/ξ^L := by
  apply normalized_jump_gevrey_of_lateral G D
  intro φ hφ hφπ
  simpa only [jumpStokesScale,WP.Analysis.piAction,Real.rpow_eq_pow] using
    WP.Analysis.actualPainleveJump_lateral_proportionality G D φ hφ hφπ

end WP.HigherOrder
