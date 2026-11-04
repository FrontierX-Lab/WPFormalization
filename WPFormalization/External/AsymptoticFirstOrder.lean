import WPFormalization.External.Painleve
import WPFormalization.External.SpecialFunctions

/-! Classical fixed first-order errors, separated from the new WP proofs.

PI-LEADING: GIKM, arXiv:1002.3634v3, PDF p.13, Eqs.(2.41)--(2.45)
prove Eq.(1.4) with an O(N^(-m-1)) error for each fixed m. At m=1,
Eq.(1.7) gives u_{1,1}*action=-1/8. In the existing real Stokes
normalization this is exactly the first estimate below. No growing-order
constant or parameter uniformity is admitted.

SF-GAMMA-RATIO: DLMF 5.11.13 and 5.11.15, fixed real shifts and x>0
tending to infinity. G_1(a,b)=(a-b)(a+b-1)/2. Constants may depend
on both shifts. The paper's endpoint matching remains a local proof.
-/
noncomputable section
namespace WP.External

@[blueprint "ext:painleve-leading"]
theorem painleve_first_correction_error :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, 2 ≤ G ∧ ∀ g ≥ G,
      |normalizedZeroInstanton g-(1-1/(8*(2*(g : ℝ)-3/2)))| ≤ C/(g : ℝ)^2 := by
  sorry

@[blueprint "ext:stirling"]
theorem gamma_ratio_first_correction_error (a b : ℝ) :
    ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      |Real.Gamma (x+a)/(Real.Gamma (x+b)*Real.rpow x (a-b))-
        (1+(a-b)*(a+b-1)/(2*x))| ≤ C/x^2 := by
  sorry

end WP.External
