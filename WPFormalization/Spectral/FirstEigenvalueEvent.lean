import WPFormalization.External.SpectralGeometry

/-! The first positive discrete eigenvalue event is exactly the event that
some enumerated discrete eigenvalue belongs to the original interval (0,epsilon).
The proof uses only the explicit spectrum ordering and initial-segment fields. -/
noncomputable section
universe u v w
namespace WP.Spectral
open WP.External

lemma first_positive_iff_exists_positive {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {H : HyperbolicCurveGeometry.{u,v,w} G}
    (S : SpectralGeometry H) {g n : ℕ} (X : G.Moduli g n (fun _ => 0)) (ε : ℝ) :
    (∃ ℓ, S.positiveEigenvalue X 1=some ℓ ∧ ℓ<ε) ↔
      ∃ j ℓ, S.positiveEigenvalue X j=some ℓ ∧ 0<ℓ ∧ ℓ<ε := by
  constructor
  · rintro ⟨ℓ,hℓ,hε⟩
    exact ⟨1,ℓ,hℓ,S.positive X 1 ℓ hℓ,hε⟩
  · rintro ⟨j,ℓ,hℓ,hpos,hε⟩
    have hj : 1 ≤ j := by
      by_contra hj
      have hz : j=0 := by omega
      rw [hz,S.index_zero X] at hℓ
      cases hℓ
    obtain ⟨ℓ₁,hℓ₁⟩ := S.initial_segment X 1 j ℓ (by norm_num) hj hℓ
    exact ⟨ℓ₁,hℓ₁,(S.ordered X 1 j ℓ₁ ℓ (by norm_num) hj hℓ₁ hℓ).trans_lt hε⟩

lemma first_positive_eigenvalue_event_eq {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {H : HyperbolicCurveGeometry.{u,v,w} G}
    (S : SpectralGeometry H) (g n : ℕ) (ε : ℝ) :
    {X : G.Moduli g n (fun _ => 0) | ∃ ℓ, S.positiveEigenvalue X 1=some ℓ ∧ ℓ<ε} =
      {X | ∃ j ℓ, S.positiveEigenvalue X j=some ℓ ∧ 0<ℓ ∧ ℓ<ε} := by
  ext X
  exact first_positive_iff_exists_positive S X ε
end WP.Spectral
