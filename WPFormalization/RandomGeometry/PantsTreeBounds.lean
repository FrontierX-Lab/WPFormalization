import Mathlib
noncomputable section
namespace WP.RandomGeometry

/-- Euler characteristic and stability force a genus-zero region with two
original cusps and one outer cut to be a single pants component. -/
lemma two_cusp_planar_piece_single (vertices edges boundaries : ℕ)
    (hpositive : 0 < vertices) (hgenus : edges + 1 = vertices)
    (hboundary : boundaries = 2 * edges + 3)
    (hstable : 3 * vertices ≤ boundaries) : vertices = 1 := by omega

/-- The exact nonnegative power of the cusp weight in the nested-tree term.
There is one planar vertex per cut edge; the root has degree d. -/
lemma planar_tree_cusp_exponent_nonneg (r d : ℕ) (a degree : Fin r → ℕ)
    (hstable : ∀ v, 3 ≤ a v + degree v)
    (hdegree : (∑ v, degree v) + d = 2*r) :
    r + d ≤ ∑ v, a v := by
  have hs : 3*r ≤ (∑ v, a v) + ∑ v, degree v := by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_comm r 3] using
      (Finset.sum_le_sum (s := Finset.univ) (fun v _ => hstable v))
  omega

/-- A nonstar cut loses at least one power of the cusp count. -/
lemma nonstar_root_degree_gap (r d : ℕ) (h : d < r) : d+1 ≤ r := h

lemma nonstar_cusp_power_le_inv (n : ℝ) (hn : 1 ≤ n) (r d : ℕ) (h : d < r) :
    n^d / n^r ≤ 1/n := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hp : n^(d+1) ≤ n^r := pow_le_pow_right₀ hn (Nat.succ_le_of_lt h)
  apply (div_le_div_iff₀ (pow_pos hn0 _) hn0).2
  simpa only [one_mul, pow_succ] using hp

end WP.RandomGeometry
