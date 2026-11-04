import WPFormalization.HigherOrder.CanonicalExtractionStatement
import WPFormalization.Marked.LogGrowth

/-! The original uniform first-order coefficient bound follows from the proved canonical extraction expansion at K=0. The actual prescribed zeroth coefficient is exactly one, including both endpoints. No frequency restriction or new mathematical premise is introduced. -/
noncomputable section
namespace WP
open Filter
open scoped Topology

theorem sharp_extraction_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ,
      |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k-1| ≤ C/complexity g p := by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,_,_,_,herr,_⟩ := HigherOrder.canonical_expansion P p hp
  obtain ⟨G,hG⟩ := eventually_atTop.1
    ((Analysis.complexity_real_tendsto_atTop p).eventually (eventually_ge_atTop H))
  refine ⟨C*B,mul_pos hC hB,G,?_⟩
  intro g hg k
  have he := herr g k 0 (hG g hg) (by simpa using mul_nonneg hc.le (Real.sqrt_nonneg (complexity g p : ℝ)))
  simpa using he

end WP
