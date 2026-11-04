import WPFormalization.Volumes.MarkedScaledFourierTail
/-! The genuine marked scaled Fourier transform has a common full L1 bound and a complement-of-central-interval Gaussian tail. -/
noncomputable section
open Set MeasureTheory
namespace WP.Analysis
lemma actual_marked_fourier_integral_tails (P:PsiTheory) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀g p:ℕ,1≤p→Stable g p→32≤complexity g p→
      ∀x∈Ioo (0:ℝ) xCritical,
        (∫t:ℝ,‖scaledMarkedFourier P g p x t‖)≤C ∧
        ∀T:ℝ,0≤T→T^2≤(complexity g p:ℝ)→
          (∫t:ℝ in (Icc (-T) T)ᶜ,‖scaledMarkedFourier P g p x t‖)≤C*Real.exp (-c*T^2) := by
  obtain ⟨c,C,hc,hC,htail⟩:=scaledMarkedFourier_uniform_tail P
  refine ⟨c,C,hc,hC,?_⟩
  intro g p hp hs hh x hx
  have hi:=scaledMarkedFourier_integrable P g p x hx
  have hzero:=htail g p hp hs hh x hx 0 (by norm_num) (by simpa using (Nat.cast_nonneg (α:=ℝ) (complexity g p)))
  have he0:{t:ℝ|0≤|t|}=Set.univ:=by ext t;simp
  rw[he0] at hzero
  refine ⟨by simpa using hzero,?_⟩
  intro T hT hTh
  apply le_trans _ (htail g p hp hs hh x hx T hT hTh)
  apply setIntegral_mono_set hi.norm.integrableOn (ae_of_all _ (fun t=>norm_nonneg _))
  apply ae_of_all
  intro t ht
  have hnot:¬(-T≤t ∧ t≤T):=by simpa using ht
  have ht':t< -T ∨ T<t:=by
    rcases not_and_or.mp hnot with h | h
    · exact Or.inl (lt_of_not_ge h)
    · exact Or.inr (lt_of_not_ge h)
  change T≤|t|
  rcases ht' with hl | hr
  · rw[abs_of_neg (by linarith)]
    linarith
  · exact hr.le.trans (le_abs_self _)
end WP.Analysis
