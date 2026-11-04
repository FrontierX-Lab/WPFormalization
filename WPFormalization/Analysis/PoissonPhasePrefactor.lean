import WPFormalization.Analysis.ExtractionFactorization
import WPFormalization.Volumes.PoissonLeadingDiagonal
noncomputable section
namespace WP.Analysis
lemma poisson_phase_prefactor_real (h x s:ℝ) (k:ℕ) (hh:0<h) (hx:0<x):
    Real.exp (h*(s-(k:ℝ)/h+((k:ℝ)/h)*Real.log (((k:ℝ)/h)/x)))*h^k/(k.factorial:ℝ)=
      Real.exp (h*s)*x⁻¹^k*WP.poissonCenter k:=by
  by_cases hk:k=0
  · subst k
    simp[WP.poissonCenter]
  have hkpos:0<(k:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero hk
  have hq:0<((k:ℝ)/h)/x:=div_pos (div_pos hkpos hh) hx
  have he:h*(s-(k:ℝ)/h+((k:ℝ)/h)*Real.log (((k:ℝ)/h)/x))=
      h*s-(k:ℝ)+(k:ℝ)*Real.log (((k:ℝ)/h)/x):=by field_simp
  rw[he,Real.exp_add,Real.exp_sub,Real.exp_nat_mul,Real.exp_log hq]
  unfold WP.poissonCenter
  have heq:(((k:ℝ)/h)/x)*h=(k:ℝ)*x⁻¹:=by field_simp
  have hp:(((k:ℝ)/h)/x)^k*h^k=((k:ℝ)*x⁻¹)^k:=by rw[←mul_pow,heq]
  rw[Real.exp_neg]
  calc
    _ = Real.exp (h*s)*((((k:ℝ)/h)/x)^k*h^k)/(Real.exp (k:ℝ)*(k.factorial:ℝ)) := by ring
    _ = _ := by rw[hp,mul_pow];ring
lemma extractionQ_factorization_positive (g p k:ℕ) (hk:k≠0)
    (hh:0<(complexity g p:ℝ)):
    let h:ℝ:=complexity g p
    let ν:ℝ:=(k:ℝ)/h
    let x:ℝ:=XR (densityY (2*ν))
    extractionQ g p k=markedModel g p 0/Real.pi*
      (Real.exp (h*extractionS x)*x⁻¹^k*poissonCenter k)*
      (extractionB p x*Real.sqrt (ν/WP.euler WP.Psi x)):=by
  dsimp only
  let h:ℝ:=complexity g p
  let ν:ℝ:=(k:ℝ)/h
  let Y:ℝ:=densityY (2*ν)
  let x:ℝ:=XR Y
  have hν:0<ν:=div_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) hh
  have hY:Y∈Set.Ico (0:ℝ) y₀:=by
    exact (densityY_spec (2*ν) (by positivity)).1
  have hm:=extraction_factorization_proof g p Y hY
  have harg:(2*(k:ℝ))/(complexity g p:ℝ)=2*ν:=by dsimp[ν,h];ring
  have hs:(k:ℝ)/(h*WP.euler WP.Psi x)=ν/WP.euler WP.Psi x:=by dsimp[ν];ring
  change extractionQ g p k=markedModel g p 0/Real.pi*
    (Real.exp (h*extractionS x)*x⁻¹^k*poissonCenter k)*
    (extractionB p x*Real.sqrt (ν/WP.euler WP.Psi x))
  simp only[extractionQ,harg,ite_eq_right hk]
  change markedModel g p Y/Real.pi*(x⁻¹^k*poissonCenter k*Real.sqrt ((k:ℝ)/(h*WP.euler WP.Psi x)))=_
  rw[hm,hs]
  ring
lemma poisson_phase_prefactor_complex (h x s:ℝ) (k:ℕ) (hh:0<h) (hx:0<x)
    (a q:ℂ) (ha:a=(s:ℂ)) (hq:q=((((k:ℝ)/h)/x:ℝ):ℂ)):
    Complex.exp ((h:ℂ)*(a-((k:ℂ)/(h:ℂ))+((k:ℂ)/(h:ℂ))*Complex.log q))*(h:ℂ)^k/(k.factorial:ℂ)=
      ((Real.exp (h*s)*x⁻¹^k*WP.poissonCenter k:ℝ):ℂ):=by
  have hqn:0≤((k:ℝ)/h)/x:=by positivity
  rw[ha,hq,←Complex.ofReal_log hqn]
  simpa only[Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add,
    Complex.ofReal_exp,Complex.ofReal_pow,Complex.ofReal_natCast] using
      congrArg Complex.ofReal (poisson_phase_prefactor_real h x s k hh hx)
lemma extractionQ_zero_exact (g p:ℕ):extractionQ g p 0=markedModel g p 0/Real.pi:=by
  have hdy:densityY 0=0:=by
    have hs:=densityY_spec 0 le_rfl
    exact density_strictMonoOn.injOn hs.1 ⟨le_rfl,y₀_pos⟩
      (hs.2.trans density_zero_value.symm)
  simp[extractionQ,hdy]
end WP.Analysis
