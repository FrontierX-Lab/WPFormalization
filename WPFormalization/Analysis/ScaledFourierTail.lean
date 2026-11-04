import WPFormalization.Analysis.SignedCoefficientFourier
/-! Exact change of variables for the tail of a scaled centered circle
transform. All endpoint changes use the atom-free Lebesgue measure; the
result applies directly to the actual marked Fourier-tail estimate. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set Complex

lemma scaledCenteredFourier_norm (f:ℂ→ℂ)(μ σ t:ℝ):
    ‖scaledCenteredFourier f μ σ t‖=(Icc (-(Real.pi*σ)) (Real.pi*σ)).indicator
      (fun t:ℝ=>‖f (Complex.exp (((t/σ:ℝ):ℂ)*Complex.I))‖) t:=by
  by_cases ht:t∈Icc (-(Real.pi*σ)) (Real.pi*σ)
  · simp only[scaledCenteredFourier,Set.indicator_of_mem ht,norm_mul]
    have he:‖Complex.exp (-(μ:ℂ)*((t/σ:ℝ):ℂ)*Complex.I)‖=1:=by
      rw[Complex.norm_exp]
      simp
    rw[he,one_mul]
  · simp only[scaledCenteredFourier,Set.indicator_of_notMem ht,norm_zero]

lemma scaledCenteredFourier_tail_change_variables (f:ℂ→ℂ)(μ σ T:ℝ)(hσ:0<σ):
    (∫t:ℝ in {t:ℝ|T≤|t|},‖scaledCenteredFourier f μ σ t‖)=
      σ*∫θ:ℝ in Ioc (-Real.pi) Real.pi ∩ {θ:ℝ|T≤σ*|θ|},
        ‖f (Complex.exp ((θ:ℂ)*Complex.I))‖:=by
  let A:Set ℝ:={t:ℝ|T≤|t|}
  let B:Set ℝ:=Icc (-(Real.pi*σ)) (Real.pi*σ)
  let C:Set ℝ:={θ:ℝ|T≤σ*|θ|}
  let F:ℝ→ℝ:=fun t=>A.indicator (fun t=>‖scaledCenteredFourier f μ σ t‖) t
  have hA:MeasurableSet A:=(isClosed_le continuous_const continuous_abs).measurableSet
  have hC:MeasurableSet C:=(isClosed_le continuous_const (by fun_prop)).measurableSet
  have he:(fun θ:ℝ=>F (σ*θ))=(Icc (-Real.pi) Real.pi).indicator
      (C.indicator (fun θ=>‖f (Complex.exp ((θ:ℂ)*Complex.I))‖)):=by
    funext θ
    have hAb:σ*θ∈A↔θ∈C:=by
      dsimp[A,C]
      rw[abs_mul,abs_of_pos hσ]
    have hBb:σ*θ∈B↔θ∈Icc (-Real.pi) Real.pi:=by
      change (-(Real.pi*σ)≤σ*θ ∧ σ*θ≤Real.pi*σ)↔(-Real.pi≤θ ∧ θ≤Real.pi)
      constructor
      · rintro ⟨hl,hr⟩
        constructor <;>nlinarith
      · rintro ⟨hl,hr⟩
        constructor <;>nlinarith
    by_cases ht:θ∈C <;>by_cases hb:θ∈Icc (-Real.pi) Real.pi
    · have h1:σ*θ∈A:=hAb.mpr ht
      have h2:σ*θ∈Icc (-(Real.pi*σ)) (Real.pi*σ):=hBb.mpr hb
      simp only[F,Set.indicator_of_mem h1,scaledCenteredFourier_norm,
        Set.indicator_of_mem h2,Set.indicator_of_mem hb,Set.indicator_of_mem ht]
      rw[show σ*θ/σ=θ by field_simp]
    · have h1:σ*θ∈A:=hAb.mpr ht
      have h2:σ*θ∉Icc (-(Real.pi*σ)) (Real.pi*σ):=fun h=>hb (hBb.mp h)
      simp only[F,Set.indicator_of_mem h1,scaledCenteredFourier_norm,
        Set.indicator_of_notMem h2,Set.indicator_of_notMem hb]
    · have h1:σ*θ∉A:=fun h=>ht (hAb.mp h)
      simp only[F,Set.indicator_of_notMem h1,Set.indicator_of_mem hb,Set.indicator_of_notMem ht]
    · have h1:σ*θ∉A:=fun h=>ht (hAb.mp h)
      simp only[F,Set.indicator_of_notMem h1,Set.indicator_of_notMem hb]
  have hscale:=Measure.integral_comp_mul_left F σ
  rw[he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    integral_indicator hC,Measure.restrict_restrict hC] at hscale
  have hcomm:C∩Ioc (-Real.pi) Real.pi=Ioc (-Real.pi) Real.pi∩C:=inter_comm _ _
  rw[hcomm] at hscale
  have hF:(∫t:ℝ,F t)=∫t:ℝ in A,‖scaledCenteredFourier f μ σ t‖:=integral_indicator hA
  rw[hF,abs_of_pos (inv_pos.mpr hσ),smul_eq_mul] at hscale
  dsimp only[C] at hscale
  change (∫t:ℝ in A,‖scaledCenteredFourier f μ σ t‖)=_
  rw[hscale]
  field_simp
end WP.Analysis
