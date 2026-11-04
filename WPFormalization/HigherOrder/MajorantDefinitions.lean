import WPFormalization.Statements.Basic

/-! Lemma C.2 using actual multivariate formal coefficients and finite substitution.
The ENNReal majorant operation is finite in each t degree; no convergence or
finiteness of the initially proposed extended coefficients is assumed. -/
noncomputable section
namespace WP
open scoped ENNReal

def multiDegree {m : ℕ} (α : Option (Fin m) →₀ ℕ) : ℕ := α.sum (fun _ n => n)

/- [t^j] Φ(t,E), for zero-constant E. Only monomials of total degree at most j contribute. -/
/- Blueprint label(s): lem:majorant
Paper v3: C.2 [PDF 77]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:majorant"]
def substitutionCoeff {R : Type*} [CommSemiring R] {m : ℕ}
    (Φ : MvPowerSeries (Option (Fin m)) R) (E : Fin m → PowerSeries R) (j : ℕ) : R :=
  ∑ α : Option (Fin m) → Fin (j+1),
    if (∑ s, (α s).val) ≤ j then
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun s => (α s).val)) Φ *
        PowerSeries.coeff j ((PowerSeries.X : PowerSeries R)^((α none).val) *
          ∏ i : Fin m, E i^((α (some i)).val))
    else 0

/- Blueprint label(s): lem:majorant
Paper v3: C.2 [PDF 77]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:majorant"]
def positiveLift {m : ℕ} (Φ : MvPowerSeries (Option (Fin m)) ℝ) :
    MvPowerSeries (Option (Fin m)) ℝ≥0∞ := fun α => ENNReal.ofReal (MvPowerSeries.coeff α Φ)

def zeroConstant {m : ℕ} (U : Fin m → PowerSeries ℝ) : Prop :=
  ∀ i, PowerSeries.coeff 0 (U i) = 0

/- Blueprint label(s): lem:majorant
Paper v3: C.2 [PDF 77]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:majorant"]
def formalFixedPoint {m : ℕ} (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (U : Fin m → PowerSeries ℝ) : Prop :=
  ∀ i j, PowerSeries.coeff j (U i) = substitutionCoeff (Φ i) U j

end WP
