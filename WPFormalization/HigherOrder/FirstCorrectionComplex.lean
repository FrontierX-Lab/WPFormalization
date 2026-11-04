import WPFormalization.Analysis.ComplexPrimitiveGluing
import WPFormalization.Analysis.TransportGammaFamily
import WPFormalization.HigherOrder.FirstCorrectionPrimitive

/-! The actual integral-defined first marked correction L_p extends holomorphically
on one convex complex neighborhood of the whole physical interval, for every p.
The proved real fundamental theorem and the genuine removable transport quotient
identify the local complex primitives with the original L_p, including endpoints.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
open WP.HigherOrder
lemma firstMarkedCorrection_common_holomorphic_extension :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ Convex ℝ Ω ∧ (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      ∃ Lhat : ℕ → ℂ → ℂ,∀ p : ℕ,AnalyticOnNhd ℂ (Lhat p) Ω ∧
        ∀ Y∈Icc (0:ℝ) y₀,Lhat p (Y:ℂ)=(firstMarkedCorrection p Y:ℂ) := by
  obtain ⟨U,hU,hcover,hq⟩ := transportGamma_family_quotient_complex_extension
  choose q hqa hqr using hq
  have hdf (p : ℕ) (Y : ℝ) (hY : Y∈Ioo (0:ℝ) y₀) :
      HasDerivAt (fun t : ℝ => (firstMarkedCorrection p t:ℂ)) (q p (Y:ℂ)) Y := by
    rw [hqr p Y ⟨hY.1.le,hY.2⟩]
    exact (firstMarkedCorrection_hasDerivAt p Y hY).ofReal_comp
  obtain ⟨V,hV,hVcover,F,hF⟩ := real_primitive_family_common_complex_extension 0 y₀ y₀_pos
    firstMarkedCorrection firstMarkedCorrection_continuousOn U hU hcover q hqa hdf
  obtain ⟨Ω,hΩ,hΩconv,hΩcover,hΩV⟩ := exists_convex_physical_neighborhood V hV hVcover
  exact ⟨Ω,hΩ,hΩconv,hΩcover,F,fun p => ⟨(hF p).1.mono hΩV,(hF p).2⟩⟩
end WP.Analysis
