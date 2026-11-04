import WPFormalization.Volumes.ExtractionLogData
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma physical_phase_correction_of_trace (S:ℂ→ℂ)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)
    (hS:AnalyticAt ℂ S (x:ℂ))
    (hSr:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ))):
    complexEuler S (x:ℂ)=(WP.Psi x:ℂ) ∧
    ∃β:ℂ→ℂ,0<WP.euler WP.Psi x ∧ AnalyticAt ℂ β 0 ∧ β 0=0 ∧
      centeredExponentialSlice S (x:ℂ) (Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ))=ᶠ[𝓝 0]
        (fun u:ℂ=>u^2*(β u-(1/2:ℂ))):=by
  have hSa:AnalyticAt ℝ extractionS x:=analyticAt_real_of_complex_trace S extractionS x hS hSr
  have hν:complexEuler S (x:ℂ)=(WP.Psi x:ℂ):=by
    have he:=iterated_complexEuler_real_trace S extractionS x hS hSa hSr 1
    simpa only[Function.iterate_one] using he.trans (congrArg Complex.ofReal (extractionS_euler_eq_Psi x hx))
  have hEgerm:WP.euler extractionS=ᶠ[𝓝 x] WP.Psi:=by
    filter_upwards[isOpen_Ioo.mem_nhds hx] with t ht
    exact extractionS_euler_eq_Psi t ht
  have hE2:((WP.euler^[2]) extractionS) x=WP.euler WP.Psi x:=by
    change x*deriv (WP.euler extractionS) x=x*deriv WP.Psi x
    rw[hEgerm.deriv_eq]
  have hvr:((complexEuler^[2]) S) (x:ℂ)=(WP.euler WP.Psi x:ℂ):=by
    rw[←hE2]
    exact iterated_complexEuler_real_trace S extractionS x hS hSa hSr 2
  have hv:0<WP.euler WP.Psi x:=mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  let c:ℂ:=Complex.I/(Real.sqrt (WP.euler WP.Psi x):ℂ)
  let φ:ℂ→ℂ:=centeredExponentialSlice S (x:ℂ) c
  have hφ:AnalyticAt ℂ φ 0:=by
    have ht:AnalyticAt ℂ (fun u:ℂ=>(x:ℂ)*Complex.exp (c*u)) 0:=by fun_prop
    exact ((hS.comp_of_eq ht (by simp)).sub analyticAt_const).sub (by fun_prop)
  have hj:=centeredExponentialSlice_jets S (x:ℂ) c hS
  have hφ2:iteratedDeriv 2 φ 0=-1:=by
    rw[hj.2.2,hvr]
    have hs:(Real.sqrt (WP.euler WP.Psi x):ℂ)^2=(WP.euler WP.Psi x:ℂ):=by
      exact_mod_cast Real.sq_sqrt hv.le
    dsimp[c]
    rw[div_pow,Complex.I_sq,hs]
    have hv0:(WP.euler WP.Psi x:ℂ)≠0:=by exact_mod_cast hv.ne'
    field_simp
  obtain ⟨G,hG,hG0,hfac⟩:=complex_analytic_quadratic_factor φ hφ hj.1 hj.2.1
  let β:ℂ→ℂ:=fun u=>G u+(1/2:ℂ)
  refine ⟨hν,β,hv,hG.add analyticAt_const,?_,?_⟩
  · dsimp[β]
    rw[hG0,hφ2]
    ring
  · filter_upwards[hfac] with u hu
    change φ u=u^2*(G u+(1/2:ℂ)-(1/2:ℂ))
    rw[hu]
    ring
end WP.Analysis
