import WPFormalization.HigherOrder.PureEndpoint
import WPFormalization.Marked.Positivity
import WPFormalization.Statements.Coefficients
/-! The actual critical inverse-cusp factor from exact string/dilaton
insertion. This is a finite identity, independent of any all-order
remainder, and will identify critical formal coefficients once C.3 is proved. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma critical_cusp_inverse_exact (P:PsiTheory) (g p:ℕ) (hg:2≤g) (hp:1≤p) :
    (cuspCorrection P g p y₀)⁻¹=1-(p:ℝ)/(5*(complexity g p:ℝ)) := by
  have hs:Stable g p:=by unfold Stable;omega
  have hw:W P g p y₀≠0:=(W_pos P g p hp hs y₀ ⟨y₀_pos.le,le_rfl⟩).ne'
  have hstep:W P g (p+1) y₀=(3*(5*(g:ℝ)-5+2*p))*W P g p y₀ := by
    unfold W
    rw[criticalAmplitude_step P g p hg]
    ring
  have hA:A y₀=(2/15:ℝ):=by norm_num[A,barH]
  have hhr:(complexity g p:ℝ)=2*(g:ℝ)+p-2 := by
    unfold complexity
    rw[Nat.cast_sub (by omega)]
    push_cast
    ring
  have hgr:(2:ℝ)≤g:=by exact_mod_cast hg
  have hpr:(1:ℝ)≤p:=by exact_mod_cast hp
  have hh:0<(complexity g p:ℝ):=by rw[hhr];linarith
  rw[cuspCorrection,hstep,hA]
  field_simp[hw,hh.ne']
  rw[hhr]
  ring
end WP.HigherOrder
