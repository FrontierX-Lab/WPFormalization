import WPFormalization.Coefficients.LogarithmicModelComparison
/-! Endpoint-uniform logarithmic comparison of the actual one-boundary model: LogarithmicComparisonProof. -/
noncomputable section
namespace WP.Coefficients
lemma log_succ_le_four_sqrt (g:ℕ)(hg:1≤g):Real.log ((g:ℝ)+1)≤4*Real.sqrt (g:ℝ):=by
  have hgR:(1:ℝ)≤g:=by exact_mod_cast hg
  have hg0:0≤(g:ℝ):=Nat.cast_nonneg g
  have ht:=Real.log_le_rpow_div (show 0≤(g:ℝ)+1 by positivity) (by norm_num:(0:ℝ)<1/2)
  rw[←Real.sqrt_eq_rpow] at ht
  have hs:Real.sqrt ((g:ℝ)+1)≤2*Real.sqrt (g:ℝ):=by
    have h1:=Real.sq_sqrt (show 0≤(g:ℝ)+1 by positivity)
    have h2:=Real.sq_sqrt hg0
    nlinarith[Real.sqrt_nonneg ((g:ℝ)+1),Real.sqrt_nonneg (g:ℝ)]
  nlinarith
end WP.Coefficients
namespace WP
lemma logarithmic_comparison_proof (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ k : ℕ, k ≤ 3*g-2 →
      |logComparisonG P g k-(g : ℝ)*logDegreeProfile ((k : ℝ)/g)| ≤ C*Real.sqrt g:=by
  obtain ⟨C₀,hC₀,hmodel⟩:=Coefficients.oneBoundaryModelJ_log_profile_uniform
  obtain ⟨C₁,hC₁,hactual⟩:=Coefficients.oneBoundaryModelJ_log_comparison P
  refine ⟨4*C₀+2*C₁,by positivity,?_⟩
  intro g hg k hk
  have hm:=hmodel g hg k hk
  have hkerr:=hactual g hg k hk
  have hNerr:=hactual g hg (3*g-2) le_rfl
  have hlog:=Coefficients.log_succ_le_four_sqrt g hg
  have hnorm:|logComparisonG P g k-(g:ℝ)*logDegreeProfile ((k:ℝ)/g)|≤
      |Real.log (Coefficients.oneBoundaryModelJ g k/(Coefficients.oneBoundaryModelJ g (3*g-2)*(g:ℝ)^(2*(3*g-2-k))))-
        (g:ℝ)*logDegreeProfile ((k:ℝ)/g)|+
      |Real.log (mixedJ P g k/Coefficients.oneBoundaryModelJ g k)|+
      |Real.log (mixedJ P g (3*g-2)/Coefficients.oneBoundaryModelJ g (3*g-2))|:=by
    rw[Coefficients.logComparisonG_eq_model_errors P g k hg hk]
    have he:(Real.log (Coefficients.oneBoundaryModelJ g k/(Coefficients.oneBoundaryModelJ g (3*g-2)*(g:ℝ)^(2*(3*g-2-k))))+
        Real.log (mixedJ P g k/Coefficients.oneBoundaryModelJ g k)-
        Real.log (mixedJ P g (3*g-2)/Coefficients.oneBoundaryModelJ g (3*g-2)))-
        (g:ℝ)*logDegreeProfile ((k:ℝ)/g)=
      ((Real.log (Coefficients.oneBoundaryModelJ g k/(Coefficients.oneBoundaryModelJ g (3*g-2)*(g:ℝ)^(2*(3*g-2-k))))-
        (g:ℝ)*logDegreeProfile ((k:ℝ)/g))+
        Real.log (mixedJ P g k/Coefficients.oneBoundaryModelJ g k))-
        Real.log (mixedJ P g (3*g-2)/Coefficients.oneBoundaryModelJ g (3*g-2)):=by ring
    rw[he]
    exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
  nlinarith[mul_le_mul_of_nonneg_left hlog hC₀.le]
end WP
