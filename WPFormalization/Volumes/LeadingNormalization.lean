import WPFormalization.Volumes.LeadingAmplitude
import WPFormalization.Volumes.PlanarInverse
/-! Exact numerical-model normalization at every positive cusp count.
The actual first derivative EGF coefficient and original leading volume are
identified with extractionQ, including k=0, before using any asymptotic theorem. -/
noncomputable section
namespace WP
open Set
lemma leadingVolume_succ_extractionQ (g k:ℕ)(hg:1≤g):
    leadingVolume g (k+1)=
      (2*Real.pi^2)^(dimension g (k+1))*(k.factorial:ℝ)*extractionQ g 1 k:=by
  have hc:(complexity g 1:ℝ)=2*(g:ℝ)-1:=by
    unfold complexity
    rw[Nat.cast_sub (by omega)]
    push_cast
    ring
  have hh:0<2*(g:ℝ)-1:=by
    have hg':(1:ℝ)≤g:=by exact_mod_cast hg
    linarith
  have hcn:complexity g 1=2*g-1:=by unfold complexity;omega
  let Y:=densityY (2*(k:ℝ)/(2*(g:ℝ)-1))
  have hY:Y∈Ico 0 y₀:=(Analysis.densityY_spec _ (by positivity)).1
  have hZ:Z Y=Real.sqrt 2*action Y:=(kernel_action_moments Y hY).2.2
  have hamp:=Analysis.marked_amplitude_one_eq_varpi Y hY
  have hM:markedModel g 1 Y=
      Real.Gamma (complexity g 1)*(4:ℝ)⁻¹^g/Real.sqrt (Real.pi*complexity g 1)*
        (Z Y)⁻¹^(complexity g 1)*varpi Y:=by
    unfold markedModel
    simp only[Nat.cast_one]
    rw[mul_assoc,mul_assoc,hamp]
    ring
  have hf0:(k.factorial:ℝ)≠0:=by positivity
  have he:Real.exp (-(k:ℝ))=(Real.exp 1)⁻¹^k:=by
    rw[Real.exp_neg,show (k:ℝ)=(k:ℝ)*1 by ring,Real.exp_nat_mul,inv_pow]
  simp only[leadingVolume,if_neg (show k+1≠0 by omega),Nat.add_sub_cancel,extractionQ,hc]
  change _=(2*Real.pi^2)^(dimension g (k+1))*(k.factorial:ℝ)*
    (markedModel g 1 Y/Real.pi*(if k=0 then 1 else
      (XR Y)⁻¹^k*poissonCenter k*Real.sqrt ((k:ℝ)/((2*(g:ℝ)-1)*euler Psi (XR Y)))))
  rw[hM,hZ,hc,hcn]
  by_cases hk:k=0
  · subst k
    simp [Y]
    ring
  · simp only[hk,ite_false,poissonCenter,he,Y]
    simp only[div_pow,mul_pow,inv_pow,div_eq_mul_inv,mul_inv_rev,inv_inv]
    field_simp[hf0]
lemma marked_one_realCoeff_volume (P:PsiTheory)(g k:ℕ):
    realCoeff (iteratedDeriv 1 (Phi P g)) k=
      volumeModel P g (k+1)/((2*Real.pi^2)^(dimension g (k+1))*(k.factorial:ℝ)):=by
  rw[realCoeff,coeff,Analysis.iteratedDeriv_iteratedDeriv_eq,
    PositiveConvolution.Phi_iteratedDeriv_zero]
  have he:((shifted P g (List.replicate (k+1) 0) 0:ℂ)/(k.factorial:ℂ)).re=
      shifted P g (List.replicate (k+1) 0) 0/(k.factorial:ℝ):=by norm_cast
  rw[he]
  simp only[volumeModel,mixedBracket,List.sum_replicate,nsmul_zero,pow_zero,one_mul,
    deficit,List.length_replicate,Nat.sub_zero]
  field_simp[Real.pi_ne_zero]

lemma volume_ratio_succ_extraction_ratio (P:PsiTheory)(g k:ℕ)(hg:1≤g):
    volumeModel P g (k+1)/leadingVolume g (k+1)=
      realCoeff (iteratedDeriv 1 (Phi P g)) k/extractionQ g 1 k:=by
  rw[marked_one_realCoeff_volume,leadingVolume_succ_extractionQ g k hg]
  simp only[div_div]
end WP
