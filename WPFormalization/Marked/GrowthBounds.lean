import WPFormalization.Statements.Marked
import WPFormalization.Weighted.ModelValidity
import WPFormalization.Analysis.TerminalUpper
import WPFormalization.Analysis.HarmonicCoefficientMajorant
/-! The actual marked generating functions have a uniform factorial bound.
The proved global ratio estimate and true harmonic coefficients give an
exponential factor times Gamma(h). Binomial and factorial inequalities absorb
it into C_p^(g+1) (2g+p)!, including every bounded stable genus. -/
noncomputable section
namespace WP
open Set
lemma W_eq_ratio_harmonic (P:PsiTheory)(g p:ℕ)(hs:Stable g p)(Y:ℝ)(hY:Y∈Icc 0 y₀):
    W P g p Y=(3:ℝ)^(complexity g p)*Real.Gamma (complexity g p)*
      harmonicCoeff Y (complexity g p) (dimension g p)*ratio P g (List.replicate p 0) Y := by
  have hst:Stable g (List.replicate p 0).length:=by simpa only[List.length_replicate] using hs
  have hm:0 < model g (List.replicate p 0) Y:=model_pos g _ Y hst hY
  calc W P g p Y=(4:ℝ)^g*(ratio P g (List.replicate p 0) Y*model g (List.replicate p 0) Y):=by
          rw[W,ratio,div_mul_cancel₀ _ hm.ne']
       _=_:=by
         unfold model
         simp only[List.length_replicate,deficit,List.sum_replicate,smul_zero,Nat.sub_zero]
         field_simp
         <;>ring
namespace Analysis
lemma ascFactorial_div_factorial (h m:ℕ):
    (h.ascFactorial m:ℝ)/(m.factorial:ℝ)=(Nat.choose (h+m-1) m:ℝ) := by
  rw[Nat.ascFactorial_eq_factorial_mul_choose',Nat.cast_mul]
  have hm:(m.factorial:ℝ)≠0:=by positivity
  field_simp
lemma harmonicCoeff_uniform_binomial_bound :∃B:ℝ,1 ≤ B ∧∀Y∈Icc (0:ℝ) y₀,∀h m:ℕ,
    harmonicCoeff Y h m ≤ B^m*(2:ℝ)^(h+m) := by
  obtain ⟨B,hB,hbound⟩:=harmonicCoeff_uniform_majorant
  refine ⟨B,hB,?_⟩
  intro Y hY h m
  calc _ ≤ (h.ascFactorial m:ℝ)*B^m/(m.factorial:ℝ):=hbound Y hY h m
       _=B^m*(Nat.choose (h+m-1) m:ℝ):=by rw[←ascFactorial_div_factorial];ring
       _ ≤ B^m*(2:ℝ)^(h+m-1):=mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.choose_le_two_pow (h+m-1) m) (by positivity)
       _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
end Analysis
lemma W_uniform_exponential_factorial (P:PsiTheory)(p:ℕ):∃C:ℝ,0 < C ∧∀g:ℕ,Stable g p→
    ∀Y∈Icc (0:ℝ) y₀,W P g p Y ≤ C^(g+1)*((2*g+p).factorial:ℝ) := by
  obtain ⟨Cr,hCr,hRatio⟩:=Analysis.ratio_uniform_global_upper P
  obtain ⟨B,hB,hCoeff⟩:=Analysis.harmonicCoeff_uniform_binomial_bound
  let T₀:ℝ:=3*(2:ℝ)^3*B^2*Real.exp Cr
  let T:ℝ:=max 1 T₀
  have hT:1 ≤ T:=le_max_left _ _
  have hTp:0 < T:=lt_of_lt_of_le zero_lt_one hT
  have hB0:0 ≤ B:=by linarith
  have hT₀:0 ≤ T₀:=by dsimp[T₀];positivity
  refine ⟨T^(p+2),by positivity,?_⟩
  intro g hs Y hY
  let h:=complexity g p
  let m:=dimension g p
  have hh:1 ≤ h:=by dsimp[h];unfold complexity;unfold Stable at hs;omega
  have hhR:0 < (h:ℝ):=by exact_mod_cast (by omega:0 < h)
  have hΓ:0 < Real.Gamma (h:ℝ):=Real.Gamma_pos_of_pos hhR
  have hst:Stable g (List.replicate p 0).length:=by simpa only[List.length_replicate] using hs
  have hd:(List.replicate p 0).sum ≤ dimension g (List.replicate p 0).length:=by simp
  have hRatio':ratio P g (List.replicate p 0) Y ≤ Real.exp (Cr*(h:ℝ)):=by
    simpa only[List.length_replicate] using hRatio g (List.replicate p 0) hst hd Y hY
  have hm:m ≤ 2*h:=by
    have hz:=(Analysis.admissible_comparison_sizes g (List.replicate p 0) hst hd).2.1
    simpa only[List.length_replicate,deficit,List.sum_replicate,smul_zero,Nat.sub_zero] using hz
  have hcm:harmonicCoeff Y h m ≤ B^(2*h)*(2:ℝ)^(3*h):=by
    calc _ ≤ B^m*(2:ℝ)^(h+m):=hCoeff Y hY h m
         _ ≤ _:=mul_le_mul (pow_le_pow_right₀ hB hm) (pow_le_pow_right₀ (by norm_num) (by omega))
           (by positivity) (by positivity)
  have hCpos:0 ≤ harmonicCoeff Y h m:=(harmonicCoeff_pos Y h m (by omega) hY).le
  have hTpow:T₀^h=(3:ℝ)^h*B^(2*h)*(2:ℝ)^(3*h)*Real.exp (Cr*(h:ℝ)):=by
    dsimp[T₀]
    rw[mul_pow,mul_pow,mul_pow,pow_mul,pow_mul,←Real.exp_nat_mul]
    rw[mul_comm (h:ℝ) Cr]
    ring
  have hw:W P g p Y ≤ Real.Gamma (h:ℝ)*T^h:=by
    rw[W_eq_ratio_harmonic P g p hs Y hY]
    change (3:ℝ)^h*Real.Gamma (h:ℝ)*harmonicCoeff Y h m*ratio P g (List.replicate p 0) Y ≤ _
    calc _ ≤ (3:ℝ)^h*Real.Gamma (h:ℝ)*harmonicCoeff Y h m*Real.exp (Cr*(h:ℝ)):=
             mul_le_mul_of_nonneg_left hRatio' (by positivity)
         _ ≤ (3:ℝ)^h*Real.Gamma (h:ℝ)*(B^(2*h)*(2:ℝ)^(3*h))*Real.exp (Cr*(h:ℝ)):=by gcongr
         _=Real.Gamma (h:ℝ)*T₀^h:=by rw[hTpow];ring
         _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT₀ (le_max_right _ _) h) hΓ.le
  have hfac:Real.Gamma (h:ℝ) ≤ ((2*g+p).factorial:ℝ):=by
    have he:h-1+1=h:=by omega
    have heR:((h-1:ℕ):ℝ)+1=(h:ℝ):=by exact_mod_cast he
    have hg:=Real.Gamma_nat_eq_factorial (h-1)
    rw[heR] at hg
    rw[hg]
    exact_mod_cast Nat.factorial_le (show h-1 ≤ 2*g+p by dsimp[h];unfold complexity;omega)
  have hsize:h ≤ (p+2)*(g+1):=by
    have ht:h ≤ 2*g+p:=by dsimp[h];unfold complexity;omega
    have hp:2*g+p ≤ (p+2)*(g+1):=by nlinarith [Nat.zero_le (p*g)]
    exact ht.trans hp
  calc W P g p Y ≤ Real.Gamma (h:ℝ)*T^h:=hw
       _ ≤ ((2*g+p).factorial:ℝ)*T^h:=mul_le_mul_of_nonneg_right hfac (by positivity)
       _ ≤ ((2*g+p).factorial:ℝ)*T^((p+2)*(g+1)):=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT hsize) (by positivity)
       _=_:=by rw[pow_mul];ring
end WP
