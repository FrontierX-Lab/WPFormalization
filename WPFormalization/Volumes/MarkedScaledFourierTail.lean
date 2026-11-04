import WPFormalization.Volumes.MarkedFourierInversion
import WPFormalization.Volumes.UniformFourierTail
import WPFormalization.Analysis.ScaledFourierTail
/-! The actual marked characteristic function has a uniform Gaussian tail
on the standardized scale, including both cusp-weight endpoint regimes.
This is the previously proved physical-circle tail under an exact change
of variables, with no local-limit assumption. -/
noncomputable section
namespace WP
open Set MeasureTheory

lemma scaledMarkedFourier_uniform_tail (P:PsiTheory):
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀g p:ℕ,1≤p→Stable g p→32≤complexity g p→
      ∀x∈Ioo (0:ℝ) xCritical,∀T:ℝ,0≤T→T^2≤(complexity g p:ℝ)→
        (∫t:ℝ in {t:ℝ|T≤|t|},‖scaledMarkedFourier P g p x t‖)≤C*Real.exp (-c*T^2):=by
  obtain ⟨c,C,hc,hC,hTail⟩:=marked_generating_fourier_tail_scaled P
  refine ⟨c,C,hc,hC,?_⟩
  intro g p hp hs hh x hx T hT0 hT
  let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
  have hhpos:0<(complexity g p:ℝ):=by exact_mod_cast (show 0<complexity g p by omega)
  have hv:0<euler Psi x:=mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hhpos hv)
  unfold scaledMarkedFourier
  rw[Analysis.scaledCenteredFourier_tail_change_variables (markedPGF P g p x) _ _ _ hσ]
  exact hTail g p hp hs hh x hx T hT0 hT
end WP
