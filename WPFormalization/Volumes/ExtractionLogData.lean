import WPFormalization.Analysis.ExtractionRawLogJets
import WPFormalization.Volumes.CompactPhaseData
import WPFormalization.Volumes.CompactPremorseModel
/-! Actual physical action, logarithmic extractionB and vanishing phase-correction germs supplying the prescribed extraction polynomial jet identities. They are constructed from the original kernels and physical inverse; no paper-specific expansion is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma exists_actual_extraction_log_data (P:PsiTheory) (p:ℕ) (x:ℝ) (hx:x ∈ Ioo (0:ℝ) xCritical) :
    ∃S B β:ℂ → ℂ,AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ B (x:ℂ) ∧
      ((fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ))) ∧
      ((fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ))) ∧
      0<WP.euler WP.Psi x ∧ AnalyticAt ℂ β 0 ∧ β 0=0 ∧
      centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))=ᶠ[𝓝 0]
        (fun u:ℂ=>u^2*(β u-(1/2:ℂ))) := by
  obtain ⟨S,L,hData⟩:=actual_compact_exponential_phase_data x x hx.1 le_rfl hx.2
  obtain ⟨hS,hL,hSr,hν,hv,hLr,hunit⟩:=hData x ⟨le_rfl,le_rfl⟩
  have hvar:0<WP.euler WP.Psi x:=mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  obtain ⟨Bc,hBc0,hBc⟩:=extractionB_complex_extension P p
  let B:ℂ → ℂ:=fun z=>Complex.log (Bc z)
  have hBcne:Bc (x:ℂ)≠0 := by rw[(hBc x ⟨hx.1.le,hx.2⟩).2];exact_mod_cast (extractionB_pos_interior p x ⟨hx.1.le,hx.2⟩).ne'
  have hB:AnalyticAt ℂ B (x:ℂ) :=
    (hBc x ⟨hx.1.le,hx.2⟩).1.clog (by
      rw[(hBc x ⟨hx.1.le,hx.2⟩).2]
      exact Or.inl (extractionB_pos_interior p x ⟨hx.1.le,hx.2⟩))
  have hBr:(fun t:ℝ=>B (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(Real.log (extractionB p t):ℂ)) := by
    filter_upwards[isOpen_Ioo.mem_nhds hx] with t ht
    dsimp only[B]
    rw[(hBc t ⟨ht.1.le,ht.2⟩).2,←Complex.ofReal_log (extractionB_pos_interior p t ⟨ht.1.le,ht.2⟩).le]
  let c:ℂ:=Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)
  let φ:ℂ → ℂ:=centeredExponentialSlice S (x:ℂ) c
  have hφ:AnalyticAt ℂ φ 0 := by
    have ht:AnalyticAt ℂ (fun u:ℂ=>(x:ℂ)*Complex.exp (c*u)) 0:=by fun_prop
    exact ((hS.comp_of_eq ht (by simp)).sub analyticAt_const).sub (by fun_prop)
  have hφjets:=centeredExponentialSlice_jets S (x:ℂ) c hS
  have hc:c=Complex.I*L (x:ℂ) := by
    rw[hLr,Complex.ofReal_inv]
    rfl
  have hφ2:iteratedDeriv 2 φ 0=-1 := by
    rw[show φ=centeredExponentialSlice S (x:ℂ) (Complex.I*L (x:ℂ)) from by rw[←hc]]
    exact centeredExponentialPhase_second S L (x:ℂ) hS hunit.self_of_nhds
  obtain ⟨G,hG,hG0,hfac⟩:=complex_analytic_quadratic_factor φ hφ hφjets.1 hφjets.2.1
  let β:ℂ → ℂ:=fun u=>G u+(1/2:ℂ)
  have hβ:AnalyticAt ℂ β 0:=hG.add analyticAt_const
  have hβ0:β 0=0 := by dsimp only[β];rw[hG0,hφ2];ring
  refine ⟨S,B,β,hS,hB,hSr,hBr,hvar,hβ,hβ0,?_⟩
  filter_upwards[hfac] with u hu
  change φ u=u^2*(G u+(1/2:ℂ)-(1/2:ℂ))
  rw[hu]
  ring
end WP.Analysis
