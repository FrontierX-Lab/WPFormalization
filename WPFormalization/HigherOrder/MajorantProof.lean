import WPFormalization.HigherOrder.MajorantConstruction
import WPFormalization.HigherOrder.MajorantBounds
import WPFormalization.HigherOrder.MajorantLifting
import WPFormalization.External.AnalyticImplicit

/-! Full proof of Lemma C.2 from the original finite-substitution specification.
The formal solution is constructed by well-founded recursion; its uniqueness,
nonnegative coefficients and extended-valued domination are proved locally.
Only convergence of that existing formal solution uses the generic classical
analytic implicit-function theorem from External.AnalyticImplicit.
-/
noncomputable section
namespace WP.Majorant
open scoped ENNReal
theorem analytic_majorant_proof (m : ℕ) (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
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
  obtain ⟨U,hUzero,hUfixed⟩ := formal_exists Φ hzero htriangular
  have hdet : Matrix.det ((1 : Matrix (Fin m) (Fin m) ℝ)-
      Matrix.of (fun i l => MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i))) ≠ 0 := by
    rw [triangular_jacobian_det Φ htriangular]
    norm_num
  have hconvAbs : ∃ r : ℝ, 0 < r ∧ ∀ i,
      Summable (fun α : Option (Fin m) →₀ ℕ => |MvPowerSeries.coeff α (Φ i)| * r^(multiDegree α)) := by
    obtain ⟨r,hr,hconvr⟩ := hconv
    refine ⟨r,hr,?_⟩
    intro i
    have he : (fun α : Option (Fin m) →₀ ℕ => |MvPowerSeries.coeff α (Φ i)| * r^(multiDegree α)) =
        (fun α => MvPowerSeries.coeff α (Φ i)*r^(multiDegree α)) := by
      funext α
      rw [abs_of_nonneg (hpos i α)]
    rw [he]
    exact hconvr i
  obtain ⟨ρ,hρ,hUconv⟩ := External.convergent_formal_implicit_solution m Φ hzero hconvAbs hdet U hUzero hUfixed
  obtain ⟨C,hC,hbound,hsum⟩ := geometric_bounds_of_absolute_convergence U ρ hρ hUconv
  refine ⟨U,hUzero,hUfixed,?_,?_,C,ρ,hC,hρ,hbound,hsum,?_⟩
  · intro V hVzero hVfixed
    exact fixedPoint_unique Φ htriangular V U hVzero hUzero hVfixed hUfixed
  · intro i j
    exact fixedPoint_nonnegative Φ hpos htriangular U hUzero hUfixed j i
  · intro e hezero he i j hj
    have hdom := extended_domination Φ hpos htriangular U hUzero hUfixed e hezero he j i
    refine ⟨hdom,?_,hdom.trans (ENNReal.ofReal_le_ofReal (hbound i j))⟩
    exact ne_top_of_le_ne_top (by simp) hdom

end WP.Majorant
