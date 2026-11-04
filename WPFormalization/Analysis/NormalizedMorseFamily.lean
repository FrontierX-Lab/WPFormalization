import WPFormalization.Analysis.CenteredExponentialPhase
import WPFormalization.Volumes.CriticalMorseForward
/-! A normalized joint analytic phase has a common pair of inverse Morse coordinates, exact quadratic conjugacies and uniform quadratic displacements. All proofs use existing Mathlib analytic inverses and genuine Hadamard factors. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma normalized_conjugacy_axis_deriv_one (F U:ℂ × ℂ → ℂ)
    (hF:AnalyticAt ℂ F (0,0)) (hU:AnalyticAt ℂ U (0,0))
    (hjet:∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0 ∧ deriv (fun u:ℂ=>F (δ,u)) 0=0 ∧
      iteratedDeriv 2 (fun u:ℂ=>F (δ,u)) 0=-1)
    (hUaxis:∀ᶠδ:ℂ in 𝓝 0,U (δ,0)=0) (hUderiv:deriv (fun w:ℂ=>U (0,w)) 0=1)
    (hconj:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),F (z.1,U z)=-z.2^2/2) :
    ∀ᶠδ:ℂ in 𝓝 0,deriv (fun w:ℂ=>U (δ,w)) 0=1 := by
  have hDU0:sndPartial U (0,0)=1 := (sndPartial_eq_deriv U (0,0) hU).trans hUderiv
  have hDUne:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),sndPartial U z≠-1 :=
    (sndPartial_analytic U (0,0) hU).continuousAt.eventually_ne (by rw[hDU0];norm_num)
  have ht:Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) :=
    (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
  filter_upwards [hjet,hUaxis,ht.eventually hF.eventually_analyticAt,
    ht.eventually hU.eventually_analyticAt,ht.eventually hconj.eventually_nhds,ht.eventually hDUne]
    with δ hj hUa hFa hUa' hcloc hne
  have hc:ContinuousAt (fun w:ℂ=>(δ,w)) 0 := by fun_prop
  have hcl:∀ᶠw:ℂ in 𝓝 0,F (δ,U (δ,w))=-w^2/2 := hc.tendsto.eventually hcloc
  have hs:=normalized_quadratic_conjugacy_deriv_sq (fun u:ℂ=>F (δ,u)) (fun w:ℂ=>U (δ,w))
    hFa.curry_right hUa'.curry_right hj.1 hj.2.1 hj.2.2 hUa hcl
  have hdn:deriv (fun w:ℂ=>U (δ,w)) 0≠-1 := by rw[←sndPartial_eq_deriv U (δ,0) hUa'];exact hne
  have hprod:(deriv (fun w:ℂ=>U (δ,w)) 0-1)*(deriv (fun w:ℂ=>U (δ,w)) 0+1)=0 := by linear_combination hs
  rcases mul_eq_zero.mp hprod with h|h
  · exact sub_eq_zero.mp h
  · exact False.elim (hdn (by linear_combination h))
lemma analytic_normalized_axis_displacement_bound (U:ℂ × ℂ → ℂ)
    (hU:AnalyticAt ℂ U (0,0)) (haxis:∀ᶠδ:ℂ in 𝓝 0,U (δ,0)=0)
    (hD:∀ᶠδ:ℂ in 𝓝 0,deriv (fun w:ℂ=>U (δ,w)) 0=1) :
    ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀δ w:ℂ,‖δ‖<ρ → ‖w‖<ρ → ‖U (δ,w)-w‖ ≤ C*‖w‖^2 := by
  let H:ℂ × ℂ → ℂ:=fun z=>U z-z.2
  have hH:AnalyticAt ℂ H (0,0):=hU.sub analyticAt_snd
  have hHz:∀ᶠδ:ℂ in 𝓝 0,H (δ,0)=0 := by filter_upwards[haxis] with δ hd;simp[H,hd]
  have hHD:∀ᶠδ:ℂ in 𝓝 0,deriv (fun w:ℂ=>H (δ,w)) 0=0 := by
    have ht:Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)) :=
      (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
    filter_upwards [hD,ht.eventually hU.eventually_analyticAt] with δ hd hu
    have hsub:HasDerivAt (fun w:ℂ=>H (δ,w)) (0:ℂ) 0 := by
      convert! hu.curry_right.differentiableAt.hasDerivAt.sub (hasDerivAt_id (0:ℂ)) using 1
      rw[hd];ring
    exact hsub.deriv
  exact analytic_parameter_quadratic_bound H hH hHz hHD

lemma exists_normalized_morse_pair (F:ℂ × ℂ → ℂ) (hF:AnalyticAt ℂ F (0,0))
    (hjet:∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0 ∧ deriv (fun u:ℂ=>F (δ,u)) 0=0 ∧
      iteratedDeriv 2 (fun u:ℂ=>F (δ,u)) 0=-1) :
    ∃U W:ℂ × ℂ → ℂ,AnalyticAt ℂ U (0,0) ∧ AnalyticAt ℂ W (0,0) ∧
      U (0,0)=0 ∧ W (0,0)=0 ∧
      (∀ᶠδ:ℂ in 𝓝 0,U (δ,0)=0 ∧ W (δ,0)=0 ∧
        deriv (fun u:ℂ=>U (δ,u)) 0=1 ∧ deriv (fun u:ℂ=>W (δ,u)) 0=1) ∧
      (∀ᶠz:ℂ × ℂ in 𝓝 (0,0),U (z.1,W z)=z.2 ∧ W (z.1,U z)=z.2 ∧
        F (z.1,U z)=-z.2^2/2 ∧ F z=-(W z)^2/2) ∧
      ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀δ u:ℂ,‖δ‖<ρ → ‖u‖<ρ →
        ‖U (δ,u)-u‖ ≤ C*‖u‖^2 ∧ ‖W (δ,u)-u‖ ≤ C*‖u‖^2 := by
  obtain ⟨U,hU,hU0,hUa,hUD,hconj⟩:=exists_joint_normalized_morse_inverse F hF
    (hjet.mono (fun δ hd=>hd.1)) (hjet.mono (fun δ hd=>hd.2.1)) hjet.self_of_nhds.2.2
  have hUDaxis:=normalized_conjugacy_axis_deriv_one F U hF hU hjet hUa hUD hconj
  obtain ⟨W,hW,hW0,hWa,hWD,hUW,hWU⟩:=analytic_joint_normalized_axis_inverse U hU hU0 hUa hUDaxis
  have hphase:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),F z=-(W z)^2/2 := by
    have ht:Tendsto (fun z:ℂ × ℂ=>(z.1,W z)) (𝓝 (0,0)) (𝓝 ((0,0):ℂ × ℂ)) := by
      simpa only[hW0] using (continuous_fst.continuousAt.prodMk hW.continuousAt).tendsto
    filter_upwards [hUW,ht.eventually hconj] with z h1 h2
    rw[h1] at h2
    exact h2
  obtain ⟨ρu,Cu,hρu,hCu,hbu⟩:=analytic_normalized_axis_displacement_bound U hU hUa hUDaxis
  obtain ⟨ρw,Cw,hρw,hCw,hbw⟩:=analytic_normalized_axis_displacement_bound W hW hWa hWD
  refine ⟨U,W,hU,hW,hU0,hW0,?_,?_,min ρu ρw,max Cu Cw,lt_min hρu hρw,
    hCu.trans_le (le_max_left _ _),?_⟩
  · filter_upwards[hUa,hWa,hUDaxis,hWD] with δ h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  · filter_upwards[hUW,hWU,hconj,hphase] with z h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  · intro δ u hδ hu
    constructor
    · exact (hbu δ u (hδ.trans_le (min_le_left _ _)) (hu.trans_le (min_le_left _ _))).trans
        (mul_le_mul_of_nonneg_right (le_max_left Cu Cw) (sq_nonneg _))
    · exact (hbw δ u (hδ.trans_le (min_le_right _ _)) (hu.trans_le (min_le_right _ _))).trans
        (mul_le_mul_of_nonneg_right (le_max_right Cu Cw) (sq_nonneg _))
lemma centeredExponentialPhase_shifted_analyticAt (S L:ℂ → ℂ) (z:ℂ)
    (hS:AnalyticAt ℂ S z) (hL:AnalyticAt ℂ L z):
    AnalyticAt ℂ (fun p:ℂ × ℂ=>centeredExponentialPhase S L (z+p.1,p.2)) (0,0) := by
  have hinner:AnalyticAt ℂ (fun p:ℂ × ℂ=>(z+p.1,p.2)) (0,0) :=
    (analyticAt_const.add analyticAt_fst).prod analyticAt_snd
  exact (centeredExponentialPhase_analyticAt S L z hS hL).comp_of_eq hinner (by simp)
lemma centeredExponentialPhase_shifted_normalized_jets (S L:ℂ → ℂ) (z:ℂ)
    (hS:AnalyticAt ℂ S z)
    (hnorm:∀ᶠq:ℂ in 𝓝 z,(L q)^2*((complexEuler^[2]) S) q=1):
    ∀ᶠt:ℂ in 𝓝 0,centeredExponentialPhase S L (z+t,0)=0 ∧
      deriv (fun u:ℂ=>centeredExponentialPhase S L (z+t,u)) 0=0 ∧
      iteratedDeriv 2 (fun u:ℂ=>centeredExponentialPhase S L (z+t,u)) 0=-1 := by
  have ht:Tendsto (fun t:ℂ=>z+t) (𝓝 0) (𝓝 z) := by
    simpa only[add_zero] using (show ContinuousAt (fun t:ℂ=>z+t) 0 by fun_prop).tendsto
  filter_upwards [ht.eventually hS.eventually_analyticAt,ht.eventually hnorm] with t ha hn
  refine ⟨?_,(centeredExponentialSlice_jets S (z+t) (Complex.I*L (z+t)) ha).2.1,
    centeredExponentialPhase_second S L (z+t) ha hn⟩
  simp [centeredExponentialPhase,centeredExponentialSlice]
end WP.Analysis
