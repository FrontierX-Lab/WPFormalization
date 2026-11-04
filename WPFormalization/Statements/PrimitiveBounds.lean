import WPFormalization.Intersection.PrimitiveUpper

noncomputable section
namespace WP

/- Lemma B.1, all positive degrees, with the exact dimension condition. -/
/- Blueprint label(s): lem:primitive-bounds
Paper v3: B.1 [PDF 69]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:primitive-bounds"]
theorem primitive_bounds (P : PsiTheory) (g : ℕ) (d : List ℕ) (hg : 1 ≤ g)
    (hn : 1 ≤ d.length) (hd : ∀ k ∈ d, 0 < k) (hdim : d.sum = dimension g d.length) :
    1/6 ≤ pureC P g d ∧ pureC P g d ≤ 1 := by
  exact ⟨pureC_primitive_lower P g d hg hn hd hdim,
    pureC_primitive_upper P g d hg hn hd hdim⟩

end WP
