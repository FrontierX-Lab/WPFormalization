import WPFormalization.Volumes.ExtractionPhasePhysical
import WPFormalization.Volumes.CriticalPuiseux
import WPFormalization.Analysis.EulerExponentialJets
import WPFormalization.Analysis.RealAnalyticTrace
/-! The actual extraction action, density, variance and inverse variance square root on a positive compact physical interval. Real traces identify every normalization, including the complex unit identity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma actual_compact_exponential_phase_data (a b:ℝ) (ha:0<a) (hab:a ≤ b) (hbc:b<xCritical) :
    ∃S L:ℂ → ℂ,∀x ∈ Icc a b,
      AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ L (x:ℂ) ∧
      (∀ᶠt:ℝ in 𝓝 x,S (t:ℂ)=(extractionS t:ℂ)) ∧
      complexEuler S (x:ℂ)=(WP.Psi x:ℂ) ∧
      ((complexEuler^[2]) S) (x:ℂ)=(WP.euler WP.Psi x:ℂ) ∧
      L (x:ℂ)=((Real.sqrt (WP.euler WP.Psi x))⁻¹:ℝ) ∧
      ∀ᶠq:ℂ in 𝓝 (x:ℂ),(L q)^2*((complexEuler^[2]) S) q=1 := by
  let b₁:ℝ:=(b+xCritical)/2
  have hbpos:0<b:=ha.trans_le hab
  have hb₁:0<b₁:=by dsimp[b₁];linarith
  have hbb₁:b<b₁:=by dsimp[b₁];linarith
  have hb₁c:b₁<xCritical:=by dsimp[b₁];linarith
  obtain ⟨Ω,hΩ,hcover,S,hS,hreal⟩:=extractionS_common_complex_extension b₁ hb₁ hb₁c
  let v:ℂ → ℂ:=(complexEuler^[2]) S
  let L:ℂ → ℂ:=fun z=>(Complex.sqrt (v z))⁻¹
  refine ⟨S,L,?_⟩
  intro x hx
  have hx0:0<x:=ha.trans_le hx.1
  have hxb:x<b₁:=hx.2.trans_lt hbb₁
  have hxc:x<xCritical:=hx.2.trans_lt hbc
  have hSx:AnalyticAt ℂ S (x:ℂ):=hS _ (hcover x ⟨hx0.le,hxb.le⟩)
  have htrace:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)) := by
    filter_upwards[isOpen_Ioo.mem_nhds (show x ∈ Ioo (0:ℝ) b₁ from ⟨hx0,hxb⟩)] with t ht
    exact hreal t ⟨ht.1.le,ht.2.le⟩
  have hSr:AnalyticAt ℝ extractionS x:=analyticAt_real_of_complex_trace S extractionS x hSx htrace
  have hν:complexEuler S (x:ℂ)=(WP.Psi x:ℂ) := by
    have he:=iterated_complexEuler_real_trace S extractionS x hSx hSr htrace 1
    have he1:WP.euler extractionS x=WP.Psi x:=extractionS_euler_eq_Psi x ⟨hx0,hxc⟩
    simpa only[Function.iterate_one,he1] using he
  have hEgerm:WP.euler extractionS=ᶠ[𝓝 x] WP.Psi := by
    filter_upwards[isOpen_Ioo.mem_nhds (show x ∈ Ioo (0:ℝ) xCritical from ⟨hx0,hxc⟩)] with t ht
    exact extractionS_euler_eq_Psi t ht
  have hE2:((WP.euler^[2]) extractionS) x=WP.euler WP.Psi x := by
    change x*deriv (WP.euler extractionS) x=x*deriv WP.Psi x
    rw[hEgerm.deriv_eq]
  have hvr:v (x:ℂ)=(WP.euler WP.Psi x:ℂ) := by
    rw[←hE2]
    exact iterated_complexEuler_real_trace S extractionS x hSx hSr htrace 2
  have hv:AnalyticAt ℂ v (x:ℂ) := by
    change AnalyticAt ℂ (complexEuler (complexEuler S)) (x:ℂ)
    exact complexEuler_analyticAt (complexEuler S) (x:ℂ) (complexEuler_analyticAt S (x:ℂ) hSx)
  have hvp:0<WP.euler WP.Psi x:=mul_pos hx0 (Psi_deriv_pos_interior x ⟨hx0.le,hxc⟩)
  have hvne:v (x:ℂ)≠0:=by rw[hvr];exact_mod_cast hvp.ne'
  have hsqrt:AnalyticAt ℂ (fun z=>Complex.sqrt (v z)) (x:ℂ) :=
    (complex_sqrt_analyticAt (by rw[hvr];exact Or.inl hvp)).comp (f:=v) hv
  have hsqreal:Complex.sqrt (v (x:ℂ))=(Real.sqrt (WP.euler WP.Psi x):ℂ) := by
    rw[hvr]
    exact Complex.sqrt_of_nonneg (by exact_mod_cast hvp.le)
  have hsqne:Complex.sqrt (v (x:ℂ))≠0 := by rw[hsqreal];exact_mod_cast (Real.sqrt_pos.mpr hvp).ne'
  have hL:AnalyticAt ℂ L (x:ℂ):=hsqrt.inv hsqne
  have hLr:L (x:ℂ)=((Real.sqrt (WP.euler WP.Psi x))⁻¹:ℝ) := by
    dsimp only[L]
    rw[hsqreal,Complex.ofReal_inv]
  refine ⟨hSx,hL,htrace,hν,hvr,hLr,?_⟩
  filter_upwards[hv.continuousAt.eventually_ne hvne] with q hq
  change (Complex.sqrt (v q))⁻¹^2*v q=1
  rw[inv_pow,complex_sqrt_sq,inv_mul_cancel₀ hq]
end WP.Analysis
