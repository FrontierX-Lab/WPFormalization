import WPFormalization.Statements.AbsolutePrefactor
import WPFormalization.Statements.UnmarkedReduction
import WPFormalization.Analysis.ThetaParameter
import WPFormalization.Analysis.ParameterDerivatives
import WPFormalization.Volumes.TransportPrimitive
/-! Exact zero-parameter normalizations for fixed-cusp volume asymptotics.
The first marked model, the actual EGF and the unmarked leading factor are
compared before any asymptotic universal constant is identified. -/
noncomputable section
namespace WP
open Set
lemma Theta_zero_parameter : Theta 0=2 := by
  rw [Theta,Analysis.Theta_eq_neg_two_T_deriv 0 ⟨le_rfl,y₀_pos⟩,Analysis.T_deriv_zero_value]
  norm_num
lemma Z_zero_parameter : Z 0=Real.sqrt 2*Real.pi/4 := by
  rw [(kernel_action_moments 0 ⟨le_rfl,y₀_pos⟩).2.2,action_zero_value]
  ring
lemma markedModel_one_zero_leading (g : ℕ) (hg : 1≤g) :
    (2*Real.pi^2)^(dimension g 1)*markedModel g 1 0/Real.pi=leadingVolume g 1 := by
  have ha : Real.rpow (r 0) (1/2:ℝ)*Real.sqrt (A 0*Theta 0)=1 := by
    rw [r_zero_parameter,A_zero_parameter,Theta_zero_parameter,Real.rpow_eq_pow,
      ←Real.sqrt_eq_rpow,←Real.sqrt_mul (by positivity : (0:ℝ)≤Real.pi^2/2)]
    have he : Real.pi^2/2*(1/Real.pi^2*2)=(1:ℝ) := by field_simp
    rw [he,Real.sqrt_one]
  have hM : markedModel g 1 0=
      Real.Gamma (complexity g 1)*(4:ℝ)⁻¹^g/Real.sqrt (Real.pi*complexity g 1)*
        (Z 0)⁻¹^(complexity g 1) := by
    unfold markedModel
    simp only [Nat.cast_one]
    rw [mul_assoc,mul_assoc,ha,mul_one]
  have hc : (complexity g 1:ℝ)=2*(g:ℝ)-1 := by
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hn : complexity g 1=2*g-1 := by unfold complexity;omega
  rw [hM,hc,hn,Z_zero_parameter]
  simp only [leadingVolume,show ¬(1:ℕ)=0 from by omega,ite_false,Nat.sub_self,
    Nat.cast_zero,mul_zero,zero_div,densityY_zero_parameter,
    Analysis.varpi_zero_value,action_zero_value,mul_one,ite_true]
  rw [show Real.sqrt 2*(Real.pi/4)=Real.sqrt 2*Real.pi/4 by ring]
  simp only [inv_pow,div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring_nf
  norm_num <;> ring
def fixedCuspLeadingScale (g n : ℕ) : ℝ :=
  (2*g+n-3).factorial*(4*Real.pi^2)^(2*g+n-3)/Real.sqrt (Real.pi*g)
lemma fixedCuspLeadingScale_one_gamma (g : ℕ) (hg : 1≤g) :
    fixedCuspLeadingScale g 1=Real.Gamma (2*(g:ℝ)-1)*
      (4*Real.pi^2)^(2*g-2)/Real.sqrt (Real.pi*g) := by
  have hk : 2*g+1-3=2*g-2 := by omega
  have he : 2*(g:ℝ)-1=((2*g-2:ℕ):ℝ)+1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [fixedCuspLeadingScale,hk,he,Real.Gamma_nat_eq_factorial]
lemma fixedCuspLeadingScale_one_unmarked (g : ℕ) (hg : 2≤g) :
    fixedCuspLeadingScale g 1=4*Real.pi^2*(2*(g:ℝ)-2)*leadingVolume g 0 := by
  rw [fixedCuspLeadingScale_one_gamma g (by omega)]
  have hh0 : 0<2*(g:ℝ)-2 := by
    have : (2:ℝ)≤g := by exact_mod_cast hg
    linarith
  have hΓ : Real.Gamma (2*(g:ℝ)-1)=
      (2*(g:ℝ)-2)*Real.Gamma (2*(g:ℝ)-2) := by
    convert Real.Gamma_add_one hh0.ne' using 1 <;> congr 1 <;> ring
  have hpow : 2*g-2=2*g-3+1 := by omega
  rw [hΓ,hpow,pow_succ]
  simp only [leadingVolume,ite_true]
  ring
lemma leadingVolume_one_over_fixed_scale (g : ℕ) (hg : 2≤g) :
    leadingVolume g 1/fixedCuspLeadingScale g 1=Real.sqrt (1+1/(2*(g:ℝ)-1)) := by
  rw [fixedCuspLeadingScale_one_unmarked g hg]
  exact unmarked_reduction_leading_proof g hg
lemma volume_one_over_leading (P : PsiTheory) (g : ℕ) (hg : 2≤g) :
    volumeModel P g 1/leadingVolume g 1=Real.pi*markedF P g 1 0/markedModel g 1 0 := by
  have hs : Stable g 1 := by unfold Stable;omega
  have h0 : (0:ℝ)∈Ico 0 y₀ := ⟨le_rfl,y₀_pos⟩
  have hflow := string_flow_proof P g 1 hs 0 h0
  rw [XR_zero] at hflow
  have hV : volumeModel P g 1=(2*Real.pi^2)^(dimension g 1)*markedF P g 1 0 := by
    simp only [volumeModel,mixedBracket,List.sum_replicate,nsmul_zero,pow_zero,one_mul,
      deficit,List.length_replicate,Nat.sub_zero]
    rw [hflow]
  have hM := (markedModel_pos_parameter g 1 hs 0 h0).ne'
  have hS : (2*Real.pi^2)^(dimension g 1)≠(0:ℝ) := by positivity
  rw [hV,←markedModel_one_zero_leading g (by omega)]
  field_simp [hM,hS,Real.pi_ne_zero]
  <;> ring
end WP
