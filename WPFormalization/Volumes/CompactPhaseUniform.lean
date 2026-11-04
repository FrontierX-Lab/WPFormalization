import WPFormalization.Volumes.CompactPhaseData
import WPFormalization.Analysis.CenteredExponentialPhase
import WPFormalization.Analysis.CompactAxisNeighborhood
/-! The actual centered action has one joint complex neighborhood and a common transverse disk on a compact physical interval. The uniform quadratic bound is proved by Hadamard division and a compact tube. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma actual_compact_phase_uniform_bound (a b:ℝ) (ha:0<a) (hab:a ≤ b) (hbc:b<xCritical) :
    ∃(S L:ℂ → ℂ)(Ω:Set ℂ)(r:ℝ),IsOpen Ω ∧
      (∀x ∈ Icc a b,(x:ℂ) ∈ Ω) ∧ 0<r ∧
      (∀x ∈ Icc a b,AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ L (x:ℂ) ∧
        (∀ᶠt:ℝ in 𝓝 x,S (t:ℂ)=(extractionS t:ℂ)) ∧
        complexEuler S (x:ℂ)=(WP.Psi x:ℂ) ∧
        ((complexEuler^[2]) S) (x:ℂ)=(WP.euler WP.Psi x:ℂ) ∧
        L (x:ℂ)=((Real.sqrt (WP.euler WP.Psi x))⁻¹:ℝ) ∧
        ∀ᶠq:ℂ in 𝓝 (x:ℂ),(L q)^2*((complexEuler^[2]) S) q=1) ∧
      ∀x ∈ Ω,∀u:ℂ,‖u‖<r → AnalyticAt ℂ (centeredExponentialPhase S L) (x,u) ∧
        ‖centeredExponentialPhase S L (x,u)‖ ≤ ‖u‖^2 := by
  obtain ⟨S,L,hdata⟩:=actual_compact_exponential_phase_data a b ha hab hbc
  let K:Set ℂ:=(fun x:ℝ=>(x:ℂ)) '' Icc a b
  have hK:IsCompact K:=isCompact_Icc.image Complex.continuous_ofReal
  have hF:∀x ∈ K,AnalyticAt ℂ (centeredExponentialPhase S L) (x,0) := by
    rintro x ⟨t,ht,rfl⟩
    exact centeredExponentialPhase_analyticAt S L (t:ℂ) (hdata t ht).1 (hdata t ht).2.1
  have hj:∀x ∈ K,∀ᶠq:ℂ in 𝓝 x,centeredExponentialPhase S L (q,0)=0 ∧
      deriv (fun u:ℂ=>centeredExponentialPhase S L (q,u)) 0=0 ∧
      iteratedDeriv 2 (fun u:ℂ=>centeredExponentialPhase S L (q,u)) 0=-1 := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨hSt,hLt,htrace,hν,hv,hLR,hunit⟩:=hdata t ht
    filter_upwards [hSt.eventually_analyticAt,hunit] with q hq hu
    exact ⟨by simp [centeredExponentialPhase,centeredExponentialSlice],
      (centeredExponentialSlice_jets S q (Complex.I*L q) hq).2.1,
      centeredExponentialPhase_second S L q hq hu⟩
  obtain ⟨Ω,hΩ,hKΩ,r,hr,hprop⟩:=compact_normalized_phase_quadratic_bound K hK
    (centeredExponentialPhase S L) hF hj
  exact ⟨S,L,Ω,r,hΩ,(fun x hx=>hKΩ ⟨x,hx,rfl⟩),hr,hdata,hprop⟩
end WP.Analysis
