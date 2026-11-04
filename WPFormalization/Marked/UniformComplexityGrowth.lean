import WPFormalization.Marked.GrowthBounds

/-! A single exponential-in-complexity Gamma bound for every actual stable marked amplitude, with no marking-dependent constant. -/
noncomputable section
namespace WP
open Set
lemma W_uniform_complexity_exponential (P : PsiTheory) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ g p : ℕ, Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      W P g p Y ≤ Real.Gamma (complexity g p:ℝ)*T^(complexity g p) := by
  obtain ⟨Cr,hCr,hRatio⟩:=Analysis.ratio_uniform_global_upper P
  obtain ⟨B,hB,hCoeff⟩:=Analysis.harmonicCoeff_uniform_binomial_bound
  let T₀:ℝ:=3*(2:ℝ)^3*B^2*Real.exp Cr
  let T:ℝ:=max 1 T₀
  have hT:1 ≤ T:=le_max_left _ _
  have hTp:0 < T:=lt_of_lt_of_le zero_lt_one hT
  have hB0:0 ≤ B:=by linarith
  have hT₀:0 ≤ T₀:=by dsimp[T₀];positivity
  refine ⟨T,hT,?_⟩
  intro g p hs Y hY
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
  exact hw
end WP
