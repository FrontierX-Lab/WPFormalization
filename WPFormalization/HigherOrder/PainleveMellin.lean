import WPFormalization.HigherOrder.PainleveJumpDefinitions
import WPFormalization.HigherOrder.PureEndpoint
import WPFormalization.Analysis.ScaledPowerSubstitution
/-! Exact real-coordinate algebra for the PI coefficient contour.
The normalized jump is the actual difference of the classical solutions, and
the action factors and Mellin exponents are computed exactly. The classical
coefficient contour is genuinely transferred to complex and real Gamma-weighted
integrals, including a uniform exponential-in-genus inner-circle error.
No uniform jump estimate is assumed or concluded by this contour identity. -/
noncomputable section
namespace WP.HigherOrder
open MeasureTheory Set
lemma painleveJumpCoordinate_scaled (t:ℝ) (ht:0<t) :
    painleveJumpCoordinate (External.painleveAction*t^(5/2:ℝ))=t^2 := by
  unfold painleveJumpCoordinate
  simp only [Real.rpow_eq_pow]
  rw [mul_div_cancel_left₀ _ painleveAction_pos.ne',←Real.rpow_mul ht.le]
  norm_num [Real.rpow_natCast]
lemma normalizedPainleveJump_scaled (G:External.PainleveAnalytic.GIKMData)
    (t:ℝ) (ht:0<t) :
    G.u 1 ((t^2:ℝ):ℂ)-G.u 0 ((t^2:ℝ):ℂ)=
      (-External.PainleveAnalytic.S₁*Complex.exp (-((External.painleveAction*t^(5/2:ℝ):ℝ):ℂ))*
        ((t^(-1/4:ℝ):ℝ):ℂ))*normalizedPainleveJump G (External.painleveAction*t^(5/2:ℝ)) := by
  have hS : External.PainleveAnalytic.S₁≠0 := by
    unfold External.PainleveAnalytic.S₁
    exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr stokesAmplitude_pos.ne')) Complex.I_ne_zero
  have hp : ((t^(-1/4:ℝ):ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne'
  have hpow : (t^2:ℝ)^(-1/8:ℝ)=t^(-1/4:ℝ) := by
    rw [←Real.rpow_natCast t 2,←Real.rpow_mul ht.le]
    norm_num
  rw [normalizedPainleveJump,painleveJumpCoordinate_scaled t ht]
  simp only [Real.rpow_eq_pow]
  rw [hpow]
  exact (mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hS)
    (Complex.exp_ne_zero _)) hp)).symm
lemma painleve_mellin_scalar_identity (g:ℕ) (hg:1≤g) (t:ℝ) (ht:0<t) :
    (External.painleveAction*(5/2)*t^(3/2:ℝ))*
      (Real.exp (-(External.painleveAction*t^(5/2:ℝ)))*
        (External.painleveAction*t^(5/2:ℝ))^(2*(g:ℝ)-3/2))=
      (5/2)*External.painleveAction^(2*(g:ℝ)-1/2)*
        Real.exp (-(External.painleveAction*t^(5/2:ℝ)))*
        ((t^(5*g-2):ℝ)*t^(-1/4:ℝ)) := by
  have hA := painleveAction_pos
  have hi : ((5*g-2:ℕ):ℝ)=5*(g:ℝ)-2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg ht.le _),←Real.rpow_mul ht.le,
    ←Real.rpow_natCast t (5*g-2),hi]
  have he : (3/2:ℝ)+(5/2)*(2*(g:ℝ)-3/2)=(5*(g:ℝ)-2)+(-1/4) := by ring
  calc
    _ = (5/2)*(External.painleveAction*External.painleveAction^(2*(g:ℝ)-3/2))*
        Real.exp (-(External.painleveAction*t^(5/2:ℝ)))*
        (t^(3/2:ℝ)*t^((5/2)*(2*(g:ℝ)-3/2))) := by ring
    _ = _ := by
      have ha : External.painleveAction*External.painleveAction^(2*(g:ℝ)-3/2)=
          External.painleveAction^(2*(g:ℝ)-1/2) := by
        calc
          _ = External.painleveAction^((1:ℝ)+(2*(g:ℝ)-3/2)) := by
            rw [Real.rpow_add hA,Real.rpow_one]
          _ = _ := by congr 1 <;> ring
      rw [ha,←Real.rpow_add ht,he,Real.rpow_add ht]
lemma painleve_mellin_pullback (G:External.PainleveAnalytic.GIKMData)
    (g:ℕ) (hg:1≤g) (t:ℝ) (ht:0<t) :
    (External.painleveAction*(5/2)*t^((5/2:ℝ)-1)) •
      (((Real.exp (-(External.painleveAction*t^(5/2:ℝ)))*
        (External.painleveAction*t^(5/2:ℝ))^(2*(g:ℝ)-1/2-1):ℝ):ℂ)*
          normalizedPainleveJump G (External.painleveAction*t^(5/2:ℝ))) =
      (-(5/2:ℂ)/External.PainleveAnalytic.S₁ *
        (External.painleveAction^(2*(g:ℝ)-1/2):ℝ))*
        (((t^(5*g-2):ℝ):ℂ)*(G.u 1 ((t^2:ℝ):ℂ)-G.u 0 ((t^2:ℝ):ℂ))) := by
  have hS : External.PainleveAnalytic.S₁≠0 := by
    unfold External.PainleveAnalytic.S₁
    exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr stokesAmplitude_pos.ne')) Complex.I_ne_zero
  have hexp : 2*(g:ℝ)-1/2-1=2*(g:ℝ)-3/2 := by ring
  rw [show (5/2:ℝ)-1=3/2 by norm_num,hexp,Complex.real_smul]
  rw [←mul_assoc,←Complex.ofReal_mul,painleve_mellin_scalar_identity g hg t ht,
    normalizedPainleveJump_scaled G t ht]
  push_cast
  field_simp [hS]

lemma painleve_mellin_integral (G:External.PainleveAnalytic.GIKMData)
    (g:ℕ) (hg:1≤g) (ρ:ℝ) (hρ:0≤ρ) :
    (∫ξ in Ioi (External.painleveAction*ρ^(5/2:ℝ)),
      (((Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1):ℝ):ℂ)*normalizedPainleveJump G ξ))=
      (-(5/2:ℂ)/External.PainleveAnalytic.S₁ *
        (External.painleveAction^(2*(g:ℝ)-1/2):ℝ))*
        (∫t in Ioi ρ,((t^(5*g-2):ℝ):ℂ)*(G.u 1 ((t^2:ℝ):ℂ)-G.u 0 ((t^2:ℝ):ℂ))) := by
  rw [WP.Analysis.integral_scaled_rpow_Ioi _ _ _ _ painleveAction_pos (by norm_num) hρ]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact painleve_mellin_pullback G g hg t (lt_of_le_of_lt hρ ht)

lemma painleve_mellin_integrable (G:External.PainleveAnalytic.GIKMData)
    (g:ℕ) (hg:1≤g) (ρ:ℝ) (hρ:0≤ρ)
    (hi : IntegrableOn (fun t:ℝ=>((t^(5*g-2):ℝ):ℂ)*
      (G.u 1 ((t^2:ℝ):ℂ)-G.u 0 ((t^2:ℝ):ℂ))) (Ioi ρ)) :
    IntegrableOn (fun ξ:ℝ=>
      (((Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1):ℝ):ℂ)*normalizedPainleveJump G ξ))
      (Ioi (External.painleveAction*ρ^(5/2:ℝ))) := by
  apply (WP.Analysis.integrable_scaled_rpow_Ioi_iff _ _ _ _ painleveAction_pos (by norm_num) hρ).mpr
  apply (hi.const_mul (-(5/2:ℂ)/External.PainleveAnalytic.S₁ *
    (External.painleveAction^(2*(g:ℝ)-1/2):ℝ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (painleve_mellin_pullback G g hg t (lt_of_le_of_lt hρ ht)).symm

lemma painleve_normalized_contour_error_identity (G:External.PainleveAnalytic.GIKMData)
    (g:ℕ) (hg:1≤g) (ρ:ℝ) (hρ:0≤ρ) :
    (External.normalizedZeroInstanton g:ℂ)-
        (∫ξ in Ioi (External.painleveAction*ρ^(5/2:ℝ)),
          (((Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1):ℝ):ℂ)*normalizedPainleveJump G ξ))/
            (Real.Gamma (2*(g:ℝ)-1/2):ℂ)=
      ((-Real.pi/External.stokesAmplitude *
        External.painleveAction^(2*(g:ℝ)-1/2)/Real.Gamma (2*(g:ℝ)-1/2):ℝ):ℂ)*
        ((zeroInstantonCoefficient g:ℂ)+(5/(2*(Real.pi:ℂ)*Complex.I))*
          ∫ t in Ioi ρ, ((t^(5*g-2):ℝ):ℂ)*
            (G.u 1 ((t^2:ℝ):ℂ)-G.u 0 ((t^2:ℝ):ℂ))) := by
  rw [painleve_mellin_integral G g hg ρ hρ]
  simp only [External.normalizedZeroInstanton,Real.rpow_eq_pow,
    External.PainleveAnalytic.S₁]
  push_cast
  have hS : (External.stokesAmplitude:ℂ)≠0 := Complex.ofReal_ne_zero.mpr stokesAmplitude_pos.ne'
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hG : (Real.Gamma (2*(g:ℝ)-1/2):ℂ)≠0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply (Real.Gamma_pos_of_pos _).ne'
    have hgr : (1:ℝ)≤g := by exact_mod_cast hg
    linarith
  field_simp [hS,hpi,hG,Complex.I_ne_zero] <;> ring


lemma painleve_normalized_mellin_contour (G:External.PainleveAnalytic.GIKMData)
    (ρ:ℝ) (hρ:G.contour_radius≤ρ) :
    ∃ C₀ D:ℝ,0<C₀ ∧ 0<D ∧ ∀g:ℕ,1≤g →
      IntegrableOn (fun ξ:ℝ=>
        (((Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1):ℝ):ℂ)*normalizedPainleveJump G ξ))
        (Ioi (External.painleveAction*ρ^(5/2:ℝ))) ∧
      ‖(External.normalizedZeroInstanton g:ℂ)-
        (∫ξ in Ioi (External.painleveAction*ρ^(5/2:ℝ)),
          (((Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1):ℝ):ℂ)*normalizedPainleveJump G ξ))/
            (Real.Gamma (2*(g:ℝ)-1/2):ℂ)‖≤
        C₀*D^g/Real.Gamma (2*(g:ℝ)-1/2) := by
  have hρp : 0<ρ := G.contour_radius_pos.trans_le hρ
  obtain ⟨C,hC,he⟩:=G.actual_coefficient_contour ρ hρ
  let C₀:ℝ:=Real.pi/External.stokesAmplitude*C/Real.sqrt External.painleveAction
  let D:ℝ:=(192/25:ℝ)*ρ^5
  have hS:=stokesAmplitude_pos
  have hA:=painleveAction_pos
  have hAs : 0<Real.sqrt External.painleveAction := Real.sqrt_pos.mpr hA
  refine ⟨C₀,D,by dsimp[C₀];positivity,by dsimp[D];positivity,?_⟩
  intro g hg
  obtain ⟨hi,herr⟩:=he g hg
  rw [integral_Ici_eq_integral_Ioi] at herr
  have hi' := (integrableOn_Ici_iff_integrableOn_Ioi).mp hi
  refine ⟨painleve_mellin_integrable G g hg ρ hρp.le hi',?_⟩
  have hν : 0<2*(g:ℝ)-1/2 := by
    have hgr : (1:ℝ)≤g := by exact_mod_cast hg
    linarith
  have hΓ:=Real.Gamma_pos_of_pos hν
  have hP:=Real.rpow_pos_of_pos hA (2*(g:ℝ)-1/2)
  have hscale : Real.pi/External.stokesAmplitude*
      External.painleveAction^(2*(g:ℝ)-1/2)/Real.Gamma (2*(g:ℝ)-1/2)≥0 := by positivity
  rw [painleve_normalized_contour_error_identity G g hg ρ hρp.le,norm_mul,
    Complex.norm_real,show (-Real.pi/External.stokesAmplitude *
      External.painleveAction^(2*(g:ℝ)-1/2)/Real.Gamma (2*(g:ℝ)-1/2):ℝ)=
      -(Real.pi/External.stokesAmplitude *
        External.painleveAction^(2*(g:ℝ)-1/2)/Real.Gamma (2*(g:ℝ)-1/2)) by ring,
    Real.norm_eq_abs,abs_neg,abs_of_nonneg hscale]
  calc
    _ ≤ (Real.pi/External.stokesAmplitude*
        External.painleveAction^(2*(g:ℝ)-1/2)/Real.Gamma (2*(g:ℝ)-1/2))*(C*ρ^(5*g)) :=
      mul_le_mul_of_nonneg_left herr hscale
    _ = C₀*D^g/Real.Gamma (2*(g:ℝ)-1/2) := by
      have hAr : External.painleveAction^(2*(g:ℝ)-1/2) =
          (192/25:ℝ)^g/Real.sqrt External.painleveAction := painleveAction_rpow g
      rw [hAr]
      dsimp [C₀,D]
      rw [mul_pow,pow_mul]
      ring


lemma painleve_real_mellin_contour (G:External.PainleveAnalytic.GIKMData)
    (ρ:ℝ) (hρ:G.contour_radius≤ρ) :
    ∃ C₀ D:ℝ,0<C₀ ∧ 0<D ∧ ∀g:ℕ,1≤g →
      IntegrableOn (fun ξ:ℝ=>
        (Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1))*realNormalizedPainleveJump G ξ)
        (Ioi (External.painleveAction*ρ^(5/2:ℝ))) ∧
      |External.normalizedZeroInstanton g-
        (∫ξ in Ioi (External.painleveAction*ρ^(5/2:ℝ)),
          (Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1))*realNormalizedPainleveJump G ξ)/
            Real.Gamma (2*(g:ℝ)-1/2)|≤
        C₀*D^g/Real.Gamma (2*(g:ℝ)-1/2) := by
  obtain ⟨C,D,hC,hD,he⟩:=painleve_normalized_mellin_contour G ρ hρ
  refine ⟨C,D,hC,hD,?_⟩
  intro g hg
  obtain ⟨hi,herr⟩:=he g hg
  have hreal : IntegrableOn (fun ξ:ℝ=>
      (Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1))*realNormalizedPainleveJump G ξ)
      (Ioi (External.painleveAction*ρ^(5/2:ℝ))) := by
    simpa only [RCLike.re_eq_complex_re,realNormalizedPainleveJump,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,sub_zero] using hi.re
  refine ⟨hreal,?_⟩
  have hIntegral :
      (∫ξ in Ioi (External.painleveAction*ρ^(5/2:ℝ)),
        (((Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1):ℝ):ℂ)*normalizedPainleveJump G ξ)).re=
      ∫ξ in Ioi (External.painleveAction*ρ^(5/2:ℝ)),
        (Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1))*realNormalizedPainleveJump G ξ := by
    simpa only [RCLike.re_eq_complex_re,realNormalizedPainleveJump,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,sub_zero] using (integral_re hi).symm
  have habs := Complex.abs_re_le_norm ((External.normalizedZeroInstanton g:ℂ)-
        (∫ξ in Ioi (External.painleveAction*ρ^(5/2:ℝ)),
          (((Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1):ℝ):ℂ)*normalizedPainleveJump G ξ))/
            (Real.Gamma (2*(g:ℝ)-1/2):ℂ))
  have hr : ((External.normalizedZeroInstanton g:ℂ)-
        (∫ξ in Ioi (External.painleveAction*ρ^(5/2:ℝ)),
          (((Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1):ℝ):ℂ)*normalizedPainleveJump G ξ))/
            (Real.Gamma (2*(g:ℝ)-1/2):ℂ)).re=
      External.normalizedZeroInstanton g-
        (∫ξ in Ioi (External.painleveAction*ρ^(5/2:ℝ)),
          (Real.exp (-ξ)*ξ^(2*(g:ℝ)-1/2-1))*realNormalizedPainleveJump G ξ)/
            Real.Gamma (2*(g:ℝ)-1/2) := by
    rw [div_eq_mul_inv,←Complex.ofReal_inv]
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      mul_zero,sub_zero,hIntegral]
    rfl
  rw [hr] at habs
  exact habs.trans herr


lemma painleve_real_jump_aestronglyMeasurable (G:External.PainleveAnalytic.GIKMData)
    (ρ:ℝ) (hρ:G.contour_radius≤ρ) :
    AEStronglyMeasurable (realNormalizedPainleveJump G)
      (volume.restrict (Ioi (External.painleveAction*ρ^(5/2:ℝ)))) := by
  obtain ⟨C,D,hC,hD,he⟩:=painleve_real_mellin_contour G ρ hρ
  have hi := (he 1 (by omega)).1
  norm_num only [Nat.cast_one,mul_one,show (2:ℝ)-1/2-1=1/2 by norm_num] at hi
  have hw : Measurable (fun ξ:ℝ=>Real.exp (-ξ)*ξ^(1/2:ℝ)) := by fun_prop
  apply (hi.aestronglyMeasurable.aemeasurable.div hw.aemeasurable).aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hρp : 0<ρ := G.contour_radius_pos.trans_le hρ
  have ha : 0<External.painleveAction*ρ^(5/2:ℝ) :=
    mul_pos painleveAction_pos (Real.rpow_pos_of_pos hρp _)
  have hξp : 0<ξ := ha.trans hξ
  have hwp : 0<Real.exp (-ξ)*ξ^(1/2:ℝ) := by positivity
  exact mul_div_cancel_left₀ _ hwp.ne'


lemma painleve_contour_radius_above (G:External.PainleveAnalytic.GIKMData) (τ:ℝ) :
    ∃ρ:ℝ,G.contour_radius≤ρ ∧ τ≤External.painleveAction*ρ^(5/2:ℝ) := by
  let y:ℝ:=max τ (External.painleveAction*G.contour_radius^(5/2:ℝ))+1
  have hy : y∈Ioi (External.painleveAction*G.contour_radius^(5/2:ℝ)) := by
    change External.painleveAction*G.contour_radius^(5/2:ℝ)<y
    dsimp [y]
    linarith [le_max_right τ (External.painleveAction*G.contour_radius^(5/2:ℝ))]
  rw [←WP.Analysis.scaled_rpow_image_Ioi External.painleveAction (5/2:ℝ) G.contour_radius
    painleveAction_pos (by norm_num) G.contour_radius_pos.le] at hy
  obtain ⟨ρ,hρ,hr⟩:=hy
  refine ⟨ρ,hρ.le,?_⟩
  change External.painleveAction*ρ^(5/2:ℝ)=y at hr
  rw [hr]
  dsimp [y]
  linarith [le_max_left τ (External.painleveAction*G.contour_radius^(5/2:ℝ))]

end WP.HigherOrder
