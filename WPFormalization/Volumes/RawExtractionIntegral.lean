import WPFormalization.Analysis.StationaryPolynomialIntegral
import WPFormalization.Analysis.ExtractionNumeratorJets
import WPFormalization.Volumes.ExtractionLogData
/-! The actual fixed-physical-parameter finite model has the original CG3 numerator expansion in its genuine real Gaussian integral. The amplitude is the canonical marked family, not a free replacement. Odd numerator coefficients vanish by exact reflection of that model. Uniform growing-order comparison with the post-Morse coefficients remains a separate obligation. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma actual_raw_gaussian_integral_fixed_order (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) (N:ℕ) :
    ∃S B β:ℂ→ℂ,∃Γ:ℕ→ℂ→ℂ,∃A:ℂ × ℂ→ℂ,∃R:ℝ,0<R ∧
      AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ B (x:ℂ) ∧ AnalyticAt ℂ β 0 ∧ β 0=0 ∧ 0<WP.euler WP.Psi x ∧
      centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))=ᶠ[𝓝 0]
        (fun u:ℂ=>u^2*(β u-(1/2:ℂ))) ∧
      ((fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ))) ∧
      ((fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ))) ∧
      (∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
        (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
          (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ))) ∧
      (∀τ u:ℂ,A (τ,u)=Complex.exp (B ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u))-B (x:ℂ))*
        ∑s∈Finset.range (N+1),τ^(2*s)*Γ s ((x:ℂ)*Complex.exp ((Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*u))) ∧
      (∀n:ℕ,n/2≤N→∀w:ℝ,WP.coeff
        (fun τ:ℂ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*A (τ,τ*(w:ℂ))) n=
        Polynomial.eval₂ Complex.ofRealHom (Complex.I*(w:ℂ)) (extractionNumeratorPolynomial P p x n)) ∧
      (∀K≤N,∃C:ℝ,0<C ∧ ∀τ:ℝ,0<τ→τ≤ min 1 (R/4)→
        ‖(∫w:ℝ in Icc (-(R/(4*τ))) (R/(4*τ)),Real.exp (-(1/2:ℝ)*w^2) •
            (Complex.exp ((w:ℂ)^2*β ((τ:ℂ)*(w:ℂ)))*A ((τ:ℂ),(τ:ℂ)*(w:ℂ))))-
          (Real.sqrt (2*Real.pi):ℂ)*∑n∈Finset.range (2*(K+1)),(τ:ℂ)^n*
            ((PowerSeries.coeff n (HigherOrder.extractionNumerator P p x):ℝ):ℂ)‖≤C*τ^(2*(K+1))) := by
  obtain ⟨S,B,β,hS,hB,hSr,hBr,hvar,hβ,hβ0,hfac⟩:=exists_actual_extraction_log_data P p x hx
  obtain ⟨Γ,hΓ⟩:=canonical_marked_weight_germ_family P p hp x hx
  let c:ℂ:=Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)
  let A:ℂ × ℂ→ℂ:=fun v=>Complex.exp (B ((x:ℂ)*Complex.exp (c*v.2))-B (x:ℂ))*
    ∑s∈Finset.range (N+1),v.1^(2*s)*Γ s ((x:ℂ)*Complex.exp (c*v.2))
  have harg:AnalyticAt ℂ (fun v:ℂ × ℂ=>(x:ℂ)*Complex.exp (c*v.2)) (0,0):=
    analyticAt_const.mul ((analyticAt_const.mul analyticAt_snd).cexp)
  have harg0:((x:ℂ)*Complex.exp (c*((0,0):ℂ × ℂ).2))=(x:ℂ):=by simp
  have hBj:AnalyticAt ℂ (fun v:ℂ × ℂ=>B ((x:ℂ)*Complex.exp (c*v.2))) (0,0):=
    hB.comp_of_eq harg harg0
  have hAj:AnalyticAt ℂ A (0,0) := by
    apply ((hBj.sub analyticAt_const).cexp).mul
    apply Finset.analyticAt_fun_sum
    intro s hs
    exact (analyticAt_fst.pow _).mul ((hΓ s).1.comp_of_eq harg harg0)
  obtain ⟨R,M,hR,hM,hstate,hF,hbound⟩:=stationary_joint_cauchy_family β A hβ hAj hβ0
  let F:ℝ→ℂ→ℂ:=fun w τ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*A (τ,τ*(w:ℂ))
  have hcoeff(n:ℕ)(hn:n/2≤N)(w:ℝ):WP.coeff (F w) n=
      Polynomial.eval₂ Complex.ofRealHom (Complex.I*(w:ℂ)) (extractionNumeratorPolynomial P p x n) := by
    have he:(F w)=(fun τ:ℂ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ))+
        (B ((x:ℂ)*Complex.exp ((Complex.I*(w:ℂ)/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ))-B (x:ℂ)))*
      (∑s∈Finset.range (N+1),τ^(2*s)*Γ s
        ((x:ℂ)*Complex.exp ((Complex.I*(w:ℂ)/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ)))) := by
      funext τ
      dsimp only[F,A,c]
      rw[show (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*(τ*(w:ℂ))=
        (Complex.I*(w:ℂ)/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ by ring,Complex.exp_add]
      ring
    rw[he]
    exact extractionNumeratorPolynomial_actual_tilt_jets P p x (w:ℂ) S B β Γ hS hB hSr hBr hvar hβ hβ0 hfac hΓ n N hn
  refine ⟨S,B,β,Γ,A,R,hR,hS,hB,hβ,hβ0,hvar,hfac,hSr,hBr,hΓ,(fun τ u=>rfl),hcoeff,?_⟩
  intro K hKN
  obtain ⟨C,hC,herror⟩:=stationary_polynomial_integral_expansion F
    (extractionNumeratorPolynomial P p x) M R hM.le hR hF hbound (2*(K+1))
    (fun n hn w=>hcoeff n (by omega) w)
  refine ⟨C,hC,?_⟩
  intro τ hτ hτsmall
  have hi:=stationary_joint_local_integrable β A R τ hR hτ (hτsmall.trans (min_le_right _ _))
    (fun u v hu hv=>⟨(hstate u v hu hv).1,(hstate u v hu hv).2.1⟩)
  have he:=herror τ hτ hτsmall hi
  have hpoly:(∑n∈Finset.range (2*(K+1)),(τ:ℂ)^n*(∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) •
      (Polynomial.map Complex.ofRealHom (extractionNumeratorPolynomial P p x n)).eval (Complex.I*(w:ℂ))))=
      (Real.sqrt (2*Real.pi):ℂ)*∑n∈Finset.range (2*(K+1)),(τ:ℂ)^n*
        ((PowerSeries.coeff n (HigherOrder.extractionNumerator P p x):ℝ):ℂ) := by
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw[extractionNumerator_gaussian_integral]
    ring
  rw[hpoly] at he
  exact he

lemma stationary_even_amplitude_parity (β:ℂ→ℂ) (a:ℕ→ℂ→ℂ) (N:ℕ) (w τ:ℂ) :
    Complex.exp ((-w)^2*β (τ*(-w)))*(∑s∈Finset.range (N+1),τ^(2*s)*a s (τ*(-w)))=
      Complex.exp (w^2*β ((-τ)*w))*(∑s∈Finset.range (N+1),(-τ)^(2*s)*a s ((-τ)*w)) := by
  simp only[neg_sq,mul_neg,neg_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw[pow_mul,pow_mul,neg_sq]

lemma extractionNumerator_odd_coefficient_zero (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) (n:ℕ) (hn:Odd n) :
    PowerSeries.coeff n (HigherOrder.extractionNumerator P p x)=0 := by
  obtain ⟨S,B,β,Γ,A,R,hR,hS,hB,hβ,hβ0,hvar,hfac,hSr,hBr,hΓ,hA,hcoeff,herror⟩:=
    actual_raw_gaussian_integral_fixed_order P p hp x hx n
  let F:ℝ→ℂ→ℂ:=fun w τ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*A (τ,τ*(w:ℂ))
  have hpar(w:ℝ):(F (-w))=(fun τ:ℂ=>F w (τ*(-1))) := by
    funext τ
    dsimp only[F]
    rw[hA,hA]
    simp only[Complex.ofReal_neg]
    have harg:(Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*(τ*(-(w:ℂ)))=
      (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))*(τ*(-1)*(w:ℂ)):=by ring
    rw[harg]
    have hbw:τ*(-(w:ℂ))=τ*(-1)*(w:ℂ):=by ring
    rw[hbw]
    simp only[neg_sq]
    congr 2
    apply Finset.sum_congr rfl
    intro s hs
    simp only[mul_pow,pow_mul,neg_sq,neg_one_sq,one_pow,mul_one]
  have hc(w:ℝ):WP.coeff (F (-w)) n= -WP.coeff (F w) n := by
    rw[hpar,coeff_complex_scale_right]
    rw[hn.neg_one_pow]
    ring
  let f:ℝ→ℂ:=fun w=>Real.exp (-(1/2:ℝ)*w^2) • WP.coeff (F w) n
  have ho(w:ℝ):f (-w)=-f w := by
    dsimp only[f]
    rw[neg_sq,hc,smul_neg]
  have he:(∫w:ℝ,f (-w))=∫w:ℝ,f w:=integral_neg_eq_self f volume
  simp_rw[ho] at he
  rw[integral_neg] at he
  have hz:(∫w:ℝ,f w)=0:=by linear_combination - (1/2:ℂ)*he
  have hi:(∫w:ℝ,f w)=(Real.sqrt (2*Real.pi):ℂ)*
      ((PowerSeries.coeff n (HigherOrder.extractionNumerator P p x):ℝ):ℂ) := by
    change (∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) • WP.coeff (F w) n)=_
    change (∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) • WP.coeff (fun τ:ℂ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*A (τ,τ*(w:ℂ))) n)=_
    simp_rw[hcoeff n (Nat.div_le_self _ _)]
    simpa only[Polynomial.eval₂_eq_eval_map] using extractionNumerator_gaussian_integral P p x n
  have hroot:(Real.sqrt (2*Real.pi):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity:0<2*Real.pi)).ne'
  rw[hi] at hz
  exact_mod_cast (mul_eq_zero.mp hz).resolve_left hroot
lemma extractionNumerator_truncation_even (P:PsiTheory) (p:ℕ) (hp:1≤p) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) (τ:ℂ) (K:ℕ) :
    (∑n∈Finset.range (2*(K+1)),τ^n*((PowerSeries.coeff n (HigherOrder.extractionNumerator P p x):ℝ):ℂ))=
      ∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)*(τ^2)^j := by
  rw[gaussian_sum_range_pairs]
  apply Finset.sum_congr rfl
  intro j hj
  rw[extractionNumerator_odd_coefficient_zero P p hp x hx (2*j+1) (by exact ⟨j,by omega⟩)]
  simp only[Complex.ofReal_zero,mul_zero,add_zero,pow_mul]
  ring
end WP.Analysis
