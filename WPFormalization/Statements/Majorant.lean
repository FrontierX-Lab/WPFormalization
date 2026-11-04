import WPFormalization.HigherOrder.MajorantProof

/-! The analytic-majorant theorem with the original full statement. -/
noncomputable section
namespace WP
open scoped ENNReal

/- Lemma C.2, including uniqueness, nonnegativity, convergence, and extended-valued domination. -/
/- Blueprint label(s): lem:majorant
Paper v3: C.2 [PDF 77]
Status: PROVED_CONDITIONALLY (generic classical analytic IFT input)
-/
@[blueprint "lem:majorant"]
theorem analytic_majorant (m : ℕ) (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (hpos : ∀ i α, 0 ≤ MvPowerSeries.coeff α (Φ i))
    (hzero : ∀ i, MvPowerSeries.coeff 0 (Φ i) = 0)
    (htriangular : ∀ i l : Fin m, i.val ≤ l.val →
      MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i) = 0)
    (hconv : ∃ r : ℝ, 0 < r ∧ ∀ i,
      Summable (fun α : Option (Fin m) →₀ ℕ => MvPowerSeries.coeff α (Φ i)*r^(multiDegree α))) :
    ∃ U : Fin m → PowerSeries ℝ,
      zeroConstant U ∧ formalFixedPoint Φ U ∧
      (∀ V : Fin m → PowerSeries ℝ, zeroConstant V → formalFixedPoint Φ V → V = U) ∧
      (∀ i j, 0 ≤ PowerSeries.coeff j (U i)) ∧
      (∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧
        (∀ i j, PowerSeries.coeff j (U i) ≤ C*ρ⁻¹^j) ∧
        (∀ i t, |t| < ρ → Summable (fun j => PowerSeries.coeff j (U i)*t^j)) ∧
        ∀ e : Fin m → ℕ → ℝ≥0∞,
          (∀ i, e i 0 = 0) →
          (∀ i j, 1 ≤ j → e i j ≤
            substitutionCoeff (positiveLift (Φ i)) (fun l => PowerSeries.mk (e l)) j) →
          ∀ i j, 1 ≤ j → e i j ≤ ENNReal.ofReal (PowerSeries.coeff j (U i)) ∧
            e i j ≠ ⊤ ∧ e i j ≤ ENNReal.ofReal (C*ρ⁻¹^j)) := by
  exact Majorant.analytic_majorant_proof m Φ hpos hzero htriangular hconv
end WP
