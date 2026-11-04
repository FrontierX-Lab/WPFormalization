import WPFormalization.Statements.Basic
noncomputable section
namespace WP

/- Removable quotient Z(u,ν)/u. -/
/- Blueprint label(s): lem:phase-change
Paper v3: D.5 [PDF 92]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:phase-change"]
def phaseQuotient (Z : ℂ × ℂ → ℂ) (u ν : ℂ) : ℂ :=
  if u = 0 then deriv (fun w => Z (w,ν)) 0 else Z (u,ν)/u

/- Blueprint label(s): lem:phase-change
Paper v3: D.5 [PDF 92]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:phase-change"]
def phaseAmplitude (Z : ℂ × ℂ → ℂ) (H : ℂ → ℂ) (z : ℂ × ℂ) : ℂ :=
  H (Z z) * deriv (fun u => Z (u,z.2)) z.1 / phaseQuotient Z z.1 z.2
end WP
