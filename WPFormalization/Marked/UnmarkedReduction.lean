import WPFormalization.Analysis.BoundaryNormalization
import WPFormalization.Analysis.ParameterODE
import WPFormalization.Statements.Volumes
import WPFormalization.Marked.Positivity

/-! The exact unmarked reduction at the zero parameter. The proof evaluates
r, A, the volume normalization and the two leading volumes from their actual
definitions, including the positive Gamma and square-root cancellations. -/
noncomputable section
namespace WP
open Set
lemma r_zero_parameter : r 0=Real.pi^2/2 := by
  have he := (stationary_root_proof 0 ⟨le_rfl,y₀_pos⟩).2.2.2
  rw [Delta,T_zero_value,sub_zero] at he
  linarith
lemma A_zero_parameter : A 0=1/Real.pi^2 := by
  have he := Analysis.J_sub_XR_eq_Aar 0 ⟨le_rfl,y₀_pos⟩
  rw [J_zero_value,XR_zero,a_zero,r_zero_parameter] at he
  apply (eq_div_iff (pow_ne_zero 2 Real.pi_ne_zero)).mpr
  nlinarith
lemma normalized_zero_parameter (P : PsiTheory) (g p : ℕ) :
    normalized P g (List.replicate p 0) 0 =
      (Real.pi^2/2)^(dimension g p)*shifted P g (List.replicate p 0) 0 := by
  simp only [normalized,show (0:ℝ)≠y₀ from (ne_of_lt y₀_pos),ite_false,a_zero,one_pow,one_mul,
    r_zero_parameter,deficit,List.sum_replicate,nsmul_zero,mul_zero,Nat.sub_zero,List.length_replicate]
lemma unmarked_reduction_volume_proof (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) :
    volumeModel P g 0 = volumeModel P g 1 *
      ((complexity g 0 : ℝ)/A 0*W P g 0 0/W P g 1 0)/(4*Real.pi^2*(2*(g:ℝ)-2)) := by
  have h0 : (0:ℝ) ∈ Icc 0 y₀ := ⟨le_rfl,y₀_pos.le⟩
  have hW := W_pos P g 1 (by omega) (by unfold Stable;omega) 0 h0
  have hU : shifted P g (List.replicate 1 0) 0 ≠ 0 := by
    intro he
    have hz : W P g 1 0=0 := by rw [W,normalized_zero_parameter,he,mul_zero,mul_zero]
    exact hW.ne' hz
  have hm : dimension g 1=dimension g 0+1 := by unfold dimension;omega
  have hh : (complexity g 0:ℝ)=2*(g:ℝ)-2 := by
    unfold complexity
    rw [Nat.add_zero,Nat.cast_sub (by omega),Nat.cast_mul]
    norm_num
  have hhp : 0<2*(g:ℝ)-2 := by
    have : (2:ℝ)≤g := by exact_mod_cast hg
    linarith
  have hg1 : (g:ℝ)-1 ≠ 0 := by linarith
  simp only [volumeModel,mixedBracket,List.sum_replicate,nsmul_zero,mul_zero,pow_zero,one_mul,
    deficit,List.length_replicate,Nat.sub_zero,W,normalized_zero_parameter,
    A_zero_parameter,hh,hm,pow_succ]
  field_simp [hU,Real.pi_ne_zero,hhp.ne',hg1]
  <;> ring
lemma densityY_zero_parameter : densityY 0=0 := by
  have hs := Analysis.densityY_spec 0 le_rfl
  exact Analysis.density_strictMonoOn.injOn hs.1 ⟨le_rfl,y₀_pos⟩
    (hs.2.trans density_zero_value.symm)
lemma leading_scalar_factor (k : ℕ) :
    (2*Real.pi^2)^(3*k+1)/(Real.pi*4^(k+1)*(Real.sqrt 2*Real.pi/4)^(2*k+1)) =
      Real.sqrt 2*(4*Real.pi^2)^(2*k) := by
  set z : ℝ := Real.sqrt 2*Real.pi/4 with hz
  have hzp : 0<z := by rw [hz];positivity
  have hzsq : z^2=Real.pi^2/8 := by
    rw [hz]
    have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
    nlinarith
  have hid : (2*Real.pi^2)^3=4*z^2*(4*Real.pi^2)^2 := by rw [hzsq];ring
  have hc : 2*Real.pi^2=Real.pi*4*z*Real.sqrt 2 := by
    rw [hz]
    have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
    nlinarith
  simp only [pow_add,pow_one,pow_mul]
  rw [hid,mul_pow,mul_pow,hc]
  field_simp [hzp.ne',Real.pi_ne_zero]
  <;> ring
lemma leadingVolume_one_closed (g : ℕ) (hg : 1 ≤ g) :
    leadingVolume g 1 = Real.Gamma (2*(g:ℝ)-1)*Real.sqrt 2*
      (4*Real.pi^2)^(2*g-2)/Real.sqrt (Real.pi*(2*(g:ℝ)-1)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show g≠0 by omega)
  simp only [Nat.succ_eq_add_one]
  have hm : dimension (k+1) 1=3*k+1 := by unfold dimension;omega
  have he : 2*(k+1)-1=2*k+1 := by omega
  have hq : 2*(k+1)-2=2*k := by omega
  simp only [leadingVolume,show ¬(1:ℕ)=0 from by omega,ite_false,ite_true,Nat.sub_self,
    Nat.cast_zero,mul_zero,zero_div,densityY_zero_parameter,hm,he,hq,
    Analysis.varpi_zero_value,action_zero_value,mul_one,ite_true]
  have hs := leading_scalar_factor k
  convert congrArg (fun x : ℝ => x*Real.Gamma (2*((k+1:ℕ):ℝ)-1)/
    Real.sqrt (Real.pi*(2*((k+1:ℕ):ℝ)-1))) hs using 1 <;> ring
lemma unmarked_reduction_leading_proof (g : ℕ) (hg : 2 ≤ g) :
    leadingVolume g 1/(4*Real.pi^2*(2*(g:ℝ)-2)*leadingVolume g 0) =
      Real.sqrt (1+1/(2*(g:ℝ)-1)) := by
  have hgR : (2:ℝ)≤g := by exact_mod_cast hg
  have hg1 : (g:ℝ)-1≠0 := by linarith
  have hh0 : 0<2*(g:ℝ)-2 := by linarith
  have hh1 : 0<2*(g:ℝ)-1 := by linarith
  have hΓ : Real.Gamma (2*(g:ℝ)-1)=
      (2*(g:ℝ)-2)*Real.Gamma (2*(g:ℝ)-2) := by
    convert Real.Gamma_add_one hh0.ne' using 1 <;> congr 1 <;> ring
  have hΓ0 := (Real.Gamma_pos_of_pos hh0).ne'
  have hΓnorm : Real.Gamma (-2+(g:ℝ)*2) ≠ 0 := by
    convert hΓ0 using 1 <;> congr 1 <;> ring
  have hpow : 2*g-2=(2*g-3)+1 := by omega
  rw [leadingVolume_one_closed g (by omega)]
  simp only [leadingVolume,ite_true]
  rw [hΓ,hpow,pow_succ]
  have he :
      ((2*(g:ℝ)-2)*Real.Gamma (2*(g:ℝ)-2)*Real.sqrt 2*
        ((4*Real.pi^2)^(2*g-3)*(4*Real.pi^2))/Real.sqrt (Real.pi*(2*(g:ℝ)-1))) /
      (4*Real.pi^2*(2*(g:ℝ)-2)*
        (Real.Gamma (2*(g:ℝ)-2)*(4*Real.pi^2)^(2*g-3)/Real.sqrt (Real.pi*g))) =
      Real.sqrt 2*Real.sqrt (Real.pi*g)/Real.sqrt (Real.pi*(2*(g:ℝ)-1)) := by
    field_simp [hΓ0,hΓnorm,hh0.ne',hg1,Real.pi_ne_zero,
      (Real.sqrt_pos.mpr (show 0<Real.pi*g by positivity)).ne',
      (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hh1)).ne']
    <;> ring_nf
    <;> simp [hΓnorm]
  rw [he]
  rw [←Real.sqrt_mul (show (0:ℝ)≤2 by norm_num),
    ←Real.sqrt_div (show 0≤2*(Real.pi*g) by positivity)]
  congr 1
  field_simp [Real.pi_ne_zero,hh1.ne']
  <;> ring
lemma unmarked_reduction_proof (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) :
    volumeModel P g 0 = volumeModel P g 1 *
      ((complexity g 0 : ℝ)/A 0*W P g 0 0/W P g 1 0)/(4*Real.pi^2*(2*(g : ℝ)-2)) ∧
    leadingVolume g 1/(4*Real.pi^2*(2*(g : ℝ)-2)*leadingVolume g 0) =
      Real.sqrt (1+1/(2*(g : ℝ)-1)) := by
  exact ⟨unmarked_reduction_volume_proof P g hg,unmarked_reduction_leading_proof g hg⟩
end WP
