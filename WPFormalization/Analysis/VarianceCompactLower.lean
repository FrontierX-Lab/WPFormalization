import WPFormalization.Analysis.ParameterInverse
/-! The actual Euler variance has a positive lower bound on every compact
subinterval strictly inside the physical cusp-weight interval. -/
noncomputable section
namespace WP.Analysis
open Set
lemma compact_eulerPsi_positive_lower (a b:ℝ)(ha:0<a)(hab:a≤b)(hb:b<xCritical):
    ∃v:ℝ,0<v ∧ ∀x∈Icc a b,v≤euler Psi x:=by
  have hc:ContinuousOn (euler Psi) (Icc a b):=by
    intro x hx
    have hxi:x∈Ico (0:ℝ) xCritical:=⟨(ha.trans_le hx.1).le,hx.2.trans_lt hb⟩
    exact (analyticAt_id.mul (Psi_analyticAt_interior x hxi).deriv).continuousAt.continuousWithinAt
  obtain ⟨x,hx,hmin⟩:=isCompact_Icc.exists_isMinOn (f:=euler Psi) ⟨a,⟨le_rfl,hab⟩⟩ hc
  have hv:0<euler Psi x:=mul_pos (ha.trans_le hx.1) (Psi_deriv_pos_interior x ⟨(ha.trans_le hx.1).le,hx.2.trans_lt hb⟩)
  exact ⟨euler Psi x,hv,fun z hz=>hmin hz⟩
end WP.Analysis
