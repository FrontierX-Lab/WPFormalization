import WPFormalization.HigherOrder.MajorantConstruction

/-! Determinant of the triangular linearization and the geometric coefficient
bound deduced from ordinary absolute convergence. These conclusions are proved
from finite matrix algebra and summability, not provided by the external IFT.
-/
noncomputable section
namespace WP.Majorant

lemma triangular_jacobian_det {m : ℕ} (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (htri : ∀ i l : Fin m, i.val ≤ l.val → MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i) = 0) :
    Matrix.det ((1 : Matrix (Fin m) (Fin m) ℝ)-
      Matrix.of (fun i l => MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i))) = 1 := by
  let M : Matrix (Fin m) (Fin m) ℝ := 1-Matrix.of (fun i l => MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i))
  have hM : M.IsLowerTriangular := by
    intro i l hil
    have hil' : i.val < l.val := hil
    have hne : i ≠ l := by intro he; subst l; omega
    simp [M,Matrix.one_apply,hne,htri i l (by omega)]
  change Matrix.det M = 1
  rw [Matrix.det_of_isLowerTriangular M hM]
  have hd : ∀ i : Fin m, M i i = 1 := by intro i; simp [M,Matrix.one_apply,htri i i (by omega)]
  simp [hd]

lemma geometric_bounds_of_absolute_convergence {m : ℕ} (U : Fin m → PowerSeries ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hU : ∀ i, Summable (fun j : ℕ => |PowerSeries.coeff j (U i)| * ρ^j)) :
    ∃ C : ℝ, 0 < C ∧ (∀ i j, PowerSeries.coeff j (U i) ≤ C*ρ⁻¹^j) ∧
      ∀ i t, |t| < ρ → Summable (fun j => PowerSeries.coeff j (U i)*t^j) := by
  let b : Fin m → ℝ := fun i => ∑' j : ℕ, |PowerSeries.coeff j (U i)| * ρ^j
  have hb : ∀ i, 0 ≤ b i := by intro i; apply tsum_nonneg; intro j; positivity
  let C : ℝ := 1+∑ i, b i
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i hi => hb i)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_,?_⟩
  · intro i j
    have hi : b i ≤ C := by
      have hs : b i ≤ ∑ k, b k := Finset.single_le_sum (fun k hk => hb k) (Finset.mem_univ i)
      dsimp [C]
      linarith
    have hj : |PowerSeries.coeff j (U i)| * ρ^j ≤ b i :=
      (hU i).le_tsum j (fun k hk => by positivity)
    calc
      PowerSeries.coeff j (U i) ≤ |PowerSeries.coeff j (U i)| := le_abs_self _
      _ ≤ C/(ρ^j) := (le_div_iff₀ (pow_pos hρ j)).2 (hj.trans hi)
      _ = C*ρ⁻¹^j := by rw [div_eq_mul_inv,inv_pow]
  · intro i t ht
    apply (hU i).of_norm_bounded
    intro j
    rw [Real.norm_eq_abs,abs_mul,abs_pow]
    gcongr

end WP.Majorant
