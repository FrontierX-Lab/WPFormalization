import WPFormalization.Tight.SeparatingCoefficientAlgebra
import WPFormalization.Tight.SeparatingDenominatorScalar
import WPFormalization.Tight.ConnectedCutLocalLimit
import WPFormalization.Tight.ConnectedPoissonPhi

noncomputable section
set_option maxHeartbeats 1600000
namespace WP.TightSeparating
open Set Filter
open scoped Topology

lemma cutProduct_coefficient_ratio_le_of_derivative_mass (P : PsiTheory) (g : ℕ)
    (hsg : Stable g 1) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) xCritical) (hF0 : 0 < markedF P g 0 x)
    (σ C K d : ℝ) (hσ : 0 < σ) (hC : 0 < C) (hK : 0 < K) (hd : 0 < d)
    (hnum : cutProductMass P gs ps L n x ≤ C/σ)
    (hden : d ≤ σ*cuspMass P g 1 (n-1) x)
    (hscalar : (n : ℝ)*markedF P g 0 x/(x*markedF P g 1 x) ≤ K) :
    realCoeff (cutProductG P gs ps L) n/realCoeff (Phi P g) n ≤
      (K*C/d)*((cutProductG P gs ps L x).re/markedF P g 0 x) := by
  have hF1 := markedF_positive_cusp_weight P g 1 (by omega) hsg x ⟨hx.1.le,hx.2⟩
  have hG := cutProductG_real_positive P gs ps hp hs L x ⟨hx.1.le,hx.2⟩
  have hmass : 0 < cuspMass P g 1 (n-1) x :=
    pos_of_mul_pos_right (hd.trans_le hden) hσ.le
  have hquot : cutProductMass P gs ps L n x/cuspMass P g 1 (n-1) x ≤ C/d := by
    apply (div_le_iff₀ hmass).mpr
    apply hnum.trans
    have hden' : d/σ ≤ cuspMass P g 1 (n-1) x := (div_le_iff₀ hσ).mpr (by nlinarith [hden])
    have he := mul_le_mul_of_nonneg_left hden' (show 0≤C/d by positivity)
    convert he using 1 <;> field_simp <;> ring
  have hscnonneg : 0 ≤ (n : ℝ)*markedF P g 0 x/(x*markedF P g 1 x) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hF0.le) (mul_nonneg hx.1.le hF1.le)
  have hfactor : ((n : ℝ)/x)*((cutProductG P gs ps L x).re/markedF P g 1 x) =
      ((n : ℝ)*markedF P g 0 x/(x*markedF P g 1 x))*
        ((cutProductG P gs ps L x).re/markedF P g 0 x) := by field_simp
  rw [cutProduct_coefficient_ratio_derivative_mass P g hsg gs ps hp hs L n hn x hx hmass.ne',hfactor]
  calc
    _ ≤ ((n : ℝ)*markedF P g 0 x/(x*markedF P g 1 x))*
        ((cutProductG P gs ps L x).re/markedF P g 0 x)*(C/d) :=
      mul_le_mul_of_nonneg_left hquot (mul_nonneg hscnonneg (div_pos hG hF0).le)
    _ ≤ K*((cutProductG P gs ps L x).re/markedF P g 0 x)*(C/d) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hscalar (div_pos hG hF0).le) (by positivity)
    _ = _ := by ring

/-- At n→∞ the genuine derivative LLT denominator and actual cut-product
point-mass bound transfer every cut numerator simultaneously to its real value.
The constant is fixed before the sequences, Q, component genera and lengths. -/
lemma separating_coefficient_transfer_unbounded (P : PsiTheory) :
    ∃ K : ℝ, 0 < K ∧ ∀ gg nn : ℕ → ℕ,
      Tendsto gg atTop atTop → Tendsto nn atTop atTop →
      (∀ j, 2 ≤ gg j) → (∀ j, 2 ≤ nn j) →
      ∀ᶠ j : ℕ in atTop, ∀ Q : ℕ, ∀ gs ps : Fin Q → ℕ,
      (∀ i, 1 ≤ ps i) → (∀ i, Stable (gs i) (ps i)) →
      (∑ i, complexity (gs i) (ps i)) = complexity (gg j) 0 →
      ∀ L : (i : Fin Q) → Fin (ps i) → ℝ,
      realCoeff (cutProductG P gs ps L) (nn j)/realCoeff (Phi P (gg j)) (nn j) ≤
        K*((cutProductG P gs ps L (TightConnected.connectedSaddle (gg j) (nn j))).re/
          markedF P (gg j) 0 (TightConnected.connectedSaddle (gg j) (nn j))) := by
  obtain ⟨K,hK,G,hscalar⟩ := separating_derivative_saddle_scalar_bound P
  obtain ⟨C,hC,hpoint⟩ := cutProduct_point_mass_bound P
  obtain ⟨G0,hF0⟩ := TightConnected.connected_unmarked_positive_eventually P
  let d : ℝ := 1/(2*Real.sqrt (2*Real.pi))
  have hd : 0 < d := by dsimp [d];positivity
  refine ⟨K*C/d,by positivity,?_⟩
  intro gg nn hg hn hg2 hn2
  filter_upwards [hg.eventually_ge_atTop (max G (max G0 10)),
    TightConnected.connectedSaddle_denominator_positive_lower P gg nn hg hn hg2 hn2]
      with j hj hden
  intro Q gs ps hp hs hsum L
  let x : ℝ := TightConnected.connectedSaddle (gg j) (nn j)
  have hx : x ∈ Ioo (0 : ℝ) xCritical :=
    (TightConnected.connectedSaddle_spec _ _ (hg2 j) (hn2 j)).1
  have hσ : 0 < Real.sqrt ((complexity (gg j) 1 : ℝ)*euler Psi x) := by
    apply Real.sqrt_pos.mpr
    apply mul_pos
    · exact_mod_cast (show 0<complexity (gg j) 1 by unfold complexity;have:=hg2 j;omega)
    · exact mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hF0' : 0 < markedF P (gg j) 0 x := hF0 _ (by omega) _ ⟨hx.1.le,hx.2⟩
  have hnum : cutProductMass P gs ps L (nn j) x ≤
      C/Real.sqrt ((complexity (gg j) 1 : ℝ)*euler Psi x) := by
    unfold cutProductMass
    exact hpoint (gg j) (by omega) Q gs ps hp hs hsum L x hx (nn j)
  have hscalar' : (nn j : ℝ)*markedF P (gg j) 0 x/(x*markedF P (gg j) 1 x) ≤ K :=
    hscalar (gg j) (by omega) x hx (nn j) (hn2 j)
      (TightConnected.connectedSaddle_spec _ _ (hg2 j) (hn2 j)).2.1
  have hden' : d ≤ Real.sqrt ((complexity (gg j) 1 : ℝ)*euler Psi x)*
      cuspMass P (gg j) 1 (nn j-1) x := hden
  exact cutProduct_coefficient_ratio_le_of_derivative_mass P (gg j)
    (by unfold Stable;have:=hg2 j;omega) gs ps hp hs L (nn j) (by have:=hn2 j;omega)
    x hx hF0' (Real.sqrt ((complexity (gg j) 1 : ℝ)*euler Psi x)) C K d
    hσ hC hK hd hnum hden' hscalar'

/-- For every fixed n, including zero, the positive Poisson denominator and
numerator probability ≤1 give a uniform transfer for every cut product. -/
lemma separating_coefficient_transfer_bounded (P : PsiTheory) (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ gg : ℕ → ℕ, Tendsto gg atTop atTop →
      ∀ᶠ j : ℕ in atTop, ∀ Q : ℕ, ∀ gs ps : Fin Q → ℕ,
      (∀ i, 1 ≤ ps i) → (∀ i, Stable (gs i) (ps i)) →
      ∀ L : (i : Fin Q) → Fin (ps i) → ℝ,
      realCoeff (cutProductG P gs ps L) n/realCoeff (Phi P (gg j)) n ≤
        K*((cutProductG P gs ps L ((c/(complexity (gg j) 0 : ℝ) : ℝ) : ℂ)).re/
          markedF P (gg j) 0 (c/(complexity (gg j) 0 : ℝ))) := by
  let d : ℝ := Real.exp (-2*c)*(2*c)^n/(2*(n.factorial : ℝ))
  have hd : 0 < d := by dsimp [d];positivity
  obtain ⟨G0,hF0⟩ := TightConnected.connected_unmarked_positive_eventually P
  refine ⟨1/d,by positivity,?_⟩
  intro gg hg
  have hh := (Analysis.complexity_real_tendsto_atTop 0).comp hg
  filter_upwards [hg.eventually_ge_atTop (G0+2),hh.eventually_gt_atTop 0,
    TightConnected.connected_small_weight_eventually (fun j => (complexity (gg j) 0 : ℝ)) hh c hc.le,
    TightConnected.connected_phi_poisson_probability_eventually_lower P n c hc gg hg]
      with j hj hhj hx hden
  intro Q gs ps hp hs L
  have hx' : c/(complexity (gg j) 0 : ℝ) ∈ Ioo (0 : ℝ) xCritical :=
    ⟨div_pos hc hhj,hx.2⟩
  have hF0' : 0 < markedF P (gg j) 0 (c/(complexity (gg j) 0 : ℝ)) :=
    hF0 (gg j) (by omega) _ hx
  have hden' : d ≤ realCoeff (Phi P (gg j)) n*(c/(complexity (gg j) 0 : ℝ))^n/
      markedF P (gg j) 0 (c/(complexity (gg j) 0 : ℝ)) := hden
  exact cutProduct_coefficient_ratio_le_of_unmarked_mass P (gg j) gs ps hp hs L n
    (c/(complexity (gg j) 0 : ℝ)) hx' hF0' d hd hden'

end WP.TightSeparating
