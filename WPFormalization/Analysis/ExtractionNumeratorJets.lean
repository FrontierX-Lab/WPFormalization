import WPFormalization.Analysis.MarkedTaylorPolynomialJets
/-! Genuine tilted-model Taylor jets equal the original prescribed CG3 numerator polynomials. Consequently their full real Gaussian integrals are the original extractionNumerator coefficients, including the imaginary-axis signs. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma coeff_product_polynomial_evaluation (f g:ℂ→ℂ) (hf:AnalyticAt ℂ f 0) (hg:AnalyticAt ℂ g 0)
    (F G:ℕ→Polynomial ℝ) (w:ℂ) (n:ℕ)
    (hF:∀i:ℕ,i≤n→WP.coeff f i=Polynomial.eval₂ Complex.ofRealHom w (F i))
    (hG:∀i:ℕ,i≤n→WP.coeff g i=Polynomial.eval₂ Complex.ofRealHom w (G i)) :
    WP.coeff (fun τ:ℂ=>f τ*g τ) n=
      Polynomial.eval₂ Complex.ofRealHom w (∑i∈Finset.range (n+1),F i*G (n-i)) := by
  rw[←taylor_coeff,taylor_mul hf hg,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only[taylor_coeff,Polynomial.eval₂_mul]
  rw[hF i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),hG (n-i) (Nat.sub_le _ _)]

lemma extractionNumeratorPolynomial_actual_tilt_jets (P:PsiTheory) (p:ℕ) (x:ℝ) (w:ℂ)
    (S B β:ℂ→ℂ) (Γ:ℕ→ℂ→ℂ)
    (hS:AnalyticAt ℂ S (x:ℂ)) (hB:AnalyticAt ℂ B (x:ℂ))
    (hSr:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)))
    (hBr:(fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ)))
    (hvar:0<WP.euler WP.Psi x) (hβ:AnalyticAt ℂ β 0) (hβ0:β 0=0)
    (hfac:centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))=ᶠ[𝓝 0]
      (fun u:ℂ=>u^2*(β u-(1/2:ℂ))))
    (hΓ:∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
      (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
        (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ)))
    (n N:ℕ) (hN:n/2≤N) :
    WP.coeff (fun τ:ℂ=>Complex.exp (w^2*β (τ*w)+
      (B ((x:ℂ)*Complex.exp ((Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ))-B (x:ℂ)))*
      (∑s∈Finset.range (N+1),τ^(2*s)*Γ s
        ((x:ℂ)*Complex.exp ((Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ)))) n=
      Polynomial.eval₂ Complex.ofRealHom (Complex.I*w) (extractionNumeratorPolynomial P p x n) := by
  let c:ℂ:=Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ)
  let E:ℂ→ℂ:=fun τ=>Complex.exp (w^2*β (τ*w)+(B ((x:ℂ)*Complex.exp (c*τ))-B (x:ℂ)))
  let H:ℂ→ℂ:=fun τ=>∑s∈Finset.range (N+1),τ^(2*s)*Γ s ((x:ℂ)*Complex.exp (c*τ))
  have hb:AnalyticAt ℂ (fun τ:ℂ=>β (τ*w)) 0:=hβ.comp_of_eq (by fun_prop) (by simp)
  have hBt:AnalyticAt ℂ (fun τ:ℂ=>B ((x:ℂ)*Complex.exp (c*τ))) 0:=hB.comp_of_eq (by fun_prop) (by simp)
  have hE:AnalyticAt ℂ E 0:=((analyticAt_const.mul hb).add (hBt.sub analyticAt_const)).cexp
  have hH:AnalyticAt ℂ H 0 := by
    apply Finset.analyticAt_fun_sum
    intro s hs
    exact (analyticAt_id.pow _).mul ((hΓ s).1.comp_of_eq (by fun_prop) (by simp))
  exact coeff_product_polynomial_evaluation E H hE hH
    (HigherOrder.extractionExpPolynomial p x) (HigherOrder.markedTaylorPolynomial P p x) (Complex.I*w) n
    (fun i hi=>extractionExpPolynomial_actual_tilt_jets p x w S B β hS hB hSr hBr hvar hβ hβ0 hfac i)
    (fun i hi=>markedTaylorPolynomial_actual_tilt_jets P p x w Γ hΓ i N (by omega))
lemma gaussian_coeff_integral_of_imaginary_polynomial (F:ℝ→ℂ→ℂ) (P:Polynomial ℝ) (n:ℕ)
    (hcoeff:∀w:ℝ,WP.coeff (F w) n=Polynomial.eval₂ Complex.ofRealHom (Complex.I*(w:ℂ)) P) :
    Integrable (fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) • WP.coeff (F w) n) ∧
      (∫w:ℝ,Real.exp (-(1/2:ℝ)*w^2) • WP.coeff (F w) n)=
        (Real.sqrt (2*Real.pi):ℂ)*(HigherOrder.gaussianFunctional P:ℂ) := by
  have he:(fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) • WP.coeff (F w) n)=
      (fun w:ℝ=>Real.exp (-(1/2:ℝ)*w^2) •
        (P.map Complex.ofRealHom).eval (Complex.I*(w:ℂ))) := by
    funext w
    rw[hcoeff,Polynomial.eval₂_eq_eval_map]
  rw[he]
  exact ⟨imaginary_gaussian_polynomial_integrable P,gaussianFunctional_integral_realization P⟩
end WP.Analysis
