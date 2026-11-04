import WPFormalization.Statements.Coefficients

/-! The original boundary polynomial definitions, separated from the targets. -/
noncomputable section
namespace WP

/-- Finite degree domain; labels are retained as Fin n indices. -/
def degreeTuples (g n : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.univ.image (fun d : Fin n → Fin (dimension g n+1) => fun i => (d i).val)).filter
    (fun d => ∑ i, d i ≤ dimension g n)

/- Blueprint label(s): prop:bounded-boundaries
Paper v3: 9.4 [PDF 44]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "prop:bounded-boundaries"]
def boundaryVolumeModel (P : PsiTheory) (g n : ℕ) (L : Fin n → ℝ) : ℝ :=
  ∑ d ∈ degreeTuples g n, mixedBracket P g (List.ofFn d) *
    ∏ i, L i^(2*d i)/((4 : ℝ)^(d i)*(2*d i+1).factorial)

end WP
