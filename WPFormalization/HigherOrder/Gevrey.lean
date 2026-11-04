import WPFormalization.Statements.Basic

/-! The numerical step used for optimal truncation in Theorems 8.2/10.2/1.1.
This bounds the explicit factorial remainder; it does not assume or prove the
paper's difficult uniform remainder estimate itself.
-/
noncomputable section
namespace WP.HigherOrder

/-- The elementary factorial-square remainder bound, with no asymptotic input. -/
theorem factorialSquared_bound (C B h : ℝ) (L : ℕ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hh : 0 < h) :
    C*B^L*(L.factorial : ℝ)^2/h^L ≤ C*(B*(L : ℝ)^2/h)^L := by
  have hf : (L.factorial : ℝ) ≤ (L : ℝ)^L := by
    exact_mod_cast Nat.factorial_le_pow L
  have hs : (L.factorial : ℝ)^2 ≤ ((L : ℝ)^L)^2 :=
    pow_le_pow_left₀ (by positivity) hf 2
  have hp : ((L : ℝ)^L)^2 = ((L : ℝ)^2)^L := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm L 2]
  calc
    _ ≤ C*B^L*((L : ℝ)^L)^2/h^L :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (mul_nonneg hC (pow_nonneg hB L)))
        (pow_nonneg hh.le L)
    _ = C*(B*(L : ℝ)^2/h)^L := by rw [hp, div_pow, mul_pow]; ring

/-- A geometric cutoff turns that explicit bound into an exponential in L. -/
theorem factorialSquared_exponential (C B h a : ℝ) (L : ℕ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hh : 0 < h)
    (hcut : B*(L : ℝ)^2/h ≤ Real.exp (-a)) :
    C*B^L*(L.factorial : ℝ)^2/h^L ≤ C*Real.exp (-a*(L : ℝ)) := by
  calc
    _ ≤ C*(B*(L : ℝ)^2/h)^L := factorialSquared_bound C B h L hC hB hh
    _ ≤ C*(Real.exp (-a))^L := by gcongr
    _ = C*Real.exp (-a*(L : ℝ)) := by rw [← Real.exp_nat_mul]; congr 2 <;> ring

/-- At the square-root cutoff, the explicit Gevrey-2 bound decays exponentially.
The hypothesis on 4Bc² is a choice of the numerical cutoff, not a paper estimate. -/
theorem factorialSquared_sqrt_cutoff (C B c h : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hc : 0 < c) (hh : 0 < h)
    (hscale : 1 ≤ c*Real.sqrt h) (hcut : 4*B*c^2 ≤ Real.exp (-1)) :
    let L := ⌊c*Real.sqrt h⌋₊+1
    C*B^L*(L.factorial : ℝ)^2/h^L ≤ C*Real.exp (-c*Real.sqrt h) := by
  dsimp only
  let L := ⌊c*Real.sqrt h⌋₊+1
  have hL : (L : ℝ) ≤ 2*c*Real.sqrt h := by
    have hf := Nat.floor_le (show 0 ≤ c*Real.sqrt h by positivity)
    simp only [L, Nat.cast_add, Nat.cast_one]
    linarith
  have hlower : c*Real.sqrt h ≤ (L : ℝ) := by
    simpa only [L, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (c*Real.sqrt h)).le
  have hs : (L : ℝ)^2 ≤ (2*c*Real.sqrt h)^2 :=
    pow_le_pow_left₀ (by positivity) hL 2
  have hbase : B*(L : ℝ)^2/h ≤ Real.exp (-1) := by
    apply le_trans _ hcut
    apply (div_le_iff₀ hh).2
    calc
      B*(L : ℝ)^2 ≤ B*(2*c*Real.sqrt h)^2 := mul_le_mul_of_nonneg_left hs hB
      _ = 4*B*c^2*h := by rw [mul_pow, mul_pow, Real.sq_sqrt hh.le]; ring
  calc
    _ ≤ C*Real.exp (-1*(L : ℝ)) :=
      factorialSquared_exponential C B h 1 L hC hB hh hbase
    _ ≤ C*Real.exp (-c*Real.sqrt h) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      linarith

end WP.HigherOrder
