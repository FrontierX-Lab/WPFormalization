import WPFormalization.Statements.Basic

/-! The original D.19/D.20 definitions and attributes, moved verbatim to avoid an import cycle. -/
noncomputable section
namespace WP

/- Blueprint label(s): lem:poisson-central
Paper v3: D.6 [PDF 93]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:poisson-central"]
def centralCoefficient (m j : ℕ) : ℂ :=
  (m.factorial : ℂ) * coeff (fun t => (Complex.log (1+t)-t)^(m-j)) m / (m-j).factorial

/- Blueprint label(s): lem:poisson-central
Paper v3: D.6 [PDF 93]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:poisson-central"]
def poissonOperator (f : ℂ × ℂ → ℂ) (h k : ℕ) : ℂ :=
  (k.factorial : ℂ)/(h : ℂ)^k * coeff (fun u => Complex.exp (h*u)*f (u,(k : ℂ)/h)) k

/- Blueprint label(s): lem:poisson-central
Paper v3: D.6 [PDF 93]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:poisson-central"]
def poissonCorrection (f : ℂ × ℂ → ℂ) (j : ℕ) (ν : ℂ) : ℂ :=
  if j = 0 then f (ν,ν) else
    ∑ m ∈ Finset.Icc (j+1) (2*j), centralCoefficient m j * ν^(m-j) *
      iteratedDeriv m (fun u => f (u,ν)) ν / m.factorial

end WP
