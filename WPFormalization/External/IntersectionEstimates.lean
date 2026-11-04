import WPFormalization.Statements.IntersectionInterface

/-! Stage-one deferred classical intersection estimates.

Source: Delecroix--Goujard--Zograf--Zorich, SIGMA 16 (2020), 086,
https://sigma-journal.com/2020/086/sigma20-086.pdf, §1, equations (4), (6).
The correlators are uniquely determined by the classical bases and Virasoro laws
(DGZZ pp.2--3). Transfer from geometric correlators to every P : PsiTheory
uses that classical uniqueness. This transfer is included in the deferred proofs
below; it has not been independently proved in Lean.
The paper's normalization C differs by a positive factor depending only on (g,n),
so the two-point comparison is unchanged. No new result of the target paper is
assumed here. The geometric instance of PsiTheory remains deferred.

One-point also appears in Liu--Xu, arXiv:1103.5136v2, p.3.
These are explicit EXTERNAL_DEFERRED theorem stubs, not Lean-verified results.
-/
noncomputable section
namespace WP

/- Known one-point formula, cited at PDF pp.53,71; interface specialization. -/
/- Blueprint label(s): ext:one-point
Paper v3: external [PDF 53]
Status: EXTERNAL_DEFERRED; geometric realization BLOCKED
-/
@[blueprint "ext:one-point"]
theorem one_point (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    pure P g [3*g-2] = 1/((24 : ℝ)^g*g.factorial) := by
  sorry

/- Published two-point bound [19, Eq.(6)], paper Appendix B; interface specialization. -/
/- Blueprint label(s): ext:two-point
Paper v3: external [PDF 69]
Status: EXTERNAL_DEFERRED; geometric realization BLOCKED
-/
@[blueprint "ext:two-point"]
theorem two_point (P : PsiTheory) (g d₁ d₂ : ℕ) (hg : 1 ≤ g)
    (hd : d₁+d₂ = 3*g-1) : pureC P g [d₁,d₂] ≤ pureC P g [0,3*g-1] := by
  sorry

end WP
