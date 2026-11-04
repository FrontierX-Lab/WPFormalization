import WPFormalization.Analysis.ExtractionPolynomialJets
import WPFormalization.Analysis.CoefficientSubstitution
import WPFormalization.Analysis.RealAnalyticTrace
import WPFormalization.Analysis.CenteredExponentialPhase
/-! The original extractionLogPolynomial and extractionExpPolynomial are the genuine jets of the normalized phase and logarithmic extractionB amplitude. The inputs are explicit analytic germs and a true quadratic phase factor, supplied by actual data in ExtractionLogData. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma coeff_quadratic_factor_shift (φ β:ℂ → ℂ) (hβ:AnalyticAt ℂ β 0)
    (hfac:φ=ᶠ[𝓝 0] (fun u:ℂ=>u^2*(β u-(1/2:ℂ)))) (n:ℕ) :
    WP.coeff φ (n+2)=WP.coeff β n-(if n=0 then (1/2:ℂ) else 0) := by
  rw [coeff_congr_of_eventuallyEq _ _ hfac (n+2),
    coeff_id_pow_mul (fun u:ℂ=>β u-(1/2:ℂ)) (hβ.sub analyticAt_const) 2 (n+2),
    ite_eq_left (by omega),show n+2-2=n by omega]
  have he:=congrArg (PowerSeries.coeff n) (taylor_sub hβ (analyticAt_const (v:=(1/2:ℂ))))
  simpa only [taylor_coeff,map_sub,taylor_const,PowerSeries.coeff_C] using he

lemma extractionLogPolynomial_actual_jets (p:ℕ) (x:ℝ) (w:ℂ) (S B β:ℂ → ℂ)
    (hS:AnalyticAt ℂ S (x:ℂ)) (hB:AnalyticAt ℂ B (x:ℂ))
    (hSr:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)))
    (hBr:(fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ)))
    (hvar:0<WP.euler WP.Psi x) (hβ:AnalyticAt ℂ β 0) (hβ0:β 0=0)
    (hfac:centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))=ᶠ[𝓝 0]
      (fun u:ℂ=>u^2*(β u-(1/2:ℂ)))) (n:ℕ) :
    WP.coeff (fun τ:ℂ=>w^2*β (τ*w)+
      (B ((x:ℂ)*Complex.exp ((Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ))-B (x:ℂ))) n=
      Polynomial.eval₂ Complex.ofRealHom (Complex.I*w) (HigherOrder.extractionLogPolynomial p x n) := by
  by_cases hn:n=0
  · subst n
    simp [WP.coeff,hβ0,HigherOrder.extractionLogPolynomial]
  let σ:ℝ:=Real.sqrt (WP.euler WP.Psi x)
  let c:ℂ:=Complex.I/(σ:ℂ)
  let cb:ℂ:=Complex.I*w/(σ:ℂ)
  have hsg:AnalyticAt ℝ extractionS x:=analyticAt_real_of_complex_trace S extractionS x hS hSr
  have hbg:AnalyticAt ℝ (fun t:ℝ=>Real.log (extractionB p t)) x:=
    analyticAt_real_of_complex_trace B _ x hB hBr
  have hshift:=coeff_quadratic_factor_shift _ β hβ hfac n
  rw[ite_eq_right hn,sub_zero] at hshift
  have hcφ:=congrArg (PowerSeries.coeff (n+2)) (centeredExponentialSlice_taylor S (x:ℂ) c hS)
  simp only[map_sub,taylor_coeff,PowerSeries.coeff_C,PowerSeries.coeff_C_mul,PowerSeries.coeff_X] at hcφ
  have hz0:n+2≠0:=by omega
  have hz1:n+2≠1:=by omega
  simp only[ite_eq_right hz0,ite_eq_right hz1,mul_zero,sub_zero] at hcφ
  have hbjet:WP.coeff β n=
      c^(n+2)*((((WP.euler^[n+2]) extractionS) x:ℝ):ℂ)/((n+2).factorial:ℂ) := by
    rw[←hshift,hcφ]
    exact coeff_exponential_tilt_real_jets S extractionS x c hS hsg hSr (n+2)
  have hBT:AnalyticAt ℂ (fun τ:ℂ=>B ((x:ℂ)*Complex.exp (cb*τ))) 0 :=
    hB.comp_of_eq (by fun_prop) (by simp)
  have hβT:AnalyticAt ℂ (fun τ:ℂ=>β (τ*w)) 0:=hβ.comp_of_eq (by fun_prop) (by simp)
  have hE:=congrArg (PowerSeries.coeff n) (taylor_add
    (f:=fun τ:ℂ=>w^2*β (τ*w)) (g:=fun τ:ℂ=>B ((x:ℂ)*Complex.exp (cb*τ))-B (x:ℂ))
    (analyticAt_const.mul hβT) (hBT.sub analyticAt_const))
  simp only[taylor_coeff,map_add,taylor_const_mul,PowerSeries.coeff_C_mul] at hE
  have hBs:=congrArg (PowerSeries.coeff n) (taylor_sub hBT (analyticAt_const (v:=B (x:ℂ))))
  simp only[taylor_coeff,map_sub,taylor_const,PowerSeries.coeff_C,ite_eq_right hn,sub_zero] at hBs
  change WP.coeff (fun τ:ℂ=>w^2*β (τ*w)+(B ((x:ℂ)*Complex.exp (cb*τ))-B (x:ℂ))) n=_
  rw[hE,hBs,coeff_complex_scale_right β w n,hbjet,
    coeff_exponential_tilt_real_jets B (fun t:ℝ=>Real.log (extractionB p t)) x cb hB hbg hBr n]
  simp only[HigherOrder.extractionLogPolynomial,ite_eq_right hn,Polynomial.eval₂_add,
    Polynomial.eval₂_monomial,Complex.ofRealHom_eq_coe]
  have hσ:(σ:ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hvar).ne'
  have hnfac:(n.factorial:ℂ)≠0:=by exact_mod_cast n.factorial_ne_zero
  have hnfac2:((n+2).factorial:ℂ)≠0:=by exact_mod_cast (n+2).factorial_ne_zero
  dsimp only[c,cb,σ] at *
  push_cast
  simp only[mul_pow,div_pow,pow_add,pow_two]
  field_simp [hσ,hnfac,hnfac2]
  <;> ring
lemma extractionExpPolynomial_actual_tilt_jets (p:ℕ) (x:ℝ) (w:ℂ) (S B β:ℂ → ℂ)
    (hS:AnalyticAt ℂ S (x:ℂ)) (hB:AnalyticAt ℂ B (x:ℂ))
    (hSr:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)))
    (hBr:(fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ)))
    (hvar:0<WP.euler WP.Psi x) (hβ:AnalyticAt ℂ β 0) (hβ0:β 0=0)
    (hfac:centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))=ᶠ[𝓝 0]
      (fun u:ℂ=>u^2*(β u-(1/2:ℂ)))) (n:ℕ) :
    WP.coeff (fun τ:ℂ=>Complex.exp (w^2*β (τ*w)+
      (B ((x:ℂ)*Complex.exp ((Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ))-B (x:ℂ)))) n=
      Polynomial.eval₂ Complex.ofRealHom (Complex.I*w) (HigherOrder.extractionExpPolynomial p x n) := by
  let E:ℂ → ℂ:=fun τ=>w^2*β (τ*w)+
    (B ((x:ℂ)*Complex.exp ((Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ))-B (x:ℂ))
  have hE:AnalyticAt ℂ E 0 := by
    have hb:AnalyticAt ℂ (fun τ:ℂ=>β (τ*w)) 0:=hβ.comp_of_eq (by fun_prop) (by simp)
    have hBtilt:AnalyticAt ℂ (fun τ:ℂ=>B ((x:ℂ)*Complex.exp ((Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ))) 0:=
      hB.comp_of_eq (by fun_prop) (by simp)
    exact (analyticAt_const.mul hb).add (hBtilt.sub analyticAt_const)
  have hE0:E 0=0:=by simp[E,hβ0]
  exact extractionExpPolynomial_eval_of_jets p x E (Complex.I*w) n hE hE0
    (fun i hi=>extractionLogPolynomial_actual_jets p x w S B β hS hB hSr hBr hvar hβ hβ0 hfac i)
end WP.Analysis
