import WPFormalization.Tight.SeparatingCutRatio
import WPFormalization.Tight.SeparatingGenusCore

noncomputable section
namespace WP.TightSeparating
open Set Finset
open scoped BigOperators

/-- Original F.8 for any actual finite stable genus family on a fixed cut
skeleton. No bound on any component genus or on the cusp density is imposed. -/
lemma separating_amplitude_genus_sum (P : PsiTheory) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Q : ℕ,
      2 ≤ Q → Q ≤ k+1 → ∀ p : Fin Q → ℕ,
      (∀ i, 1 ≤ p i) → (∑ i, p i = 2*k) →
      ∀ s : Finset (Fin Q → ℕ),
      (∀ a ∈ s, (∀ i, Stable (a i) (p i)) ∧
        (∑ i, complexity (a i) (p i)) = complexity g 0 ∧
        (∑ i, a i)+k = g+(Q-1)) →
      ∀ Y ∈ Ico (0 : ℝ) y₀,
      (∑ a ∈ s, ∏ i, markedF P (a i) (p i) (XR Y)) / markedF P g 0 (XR Y) ≤
        C * (r Y)^k / (g : ℝ)^(Q-1) := by
  obtain ⟨A,hA,G,hprod⟩ := separating_amplitude_product_bound P k
  let D : ℝ := Real.sqrt (k+1 : ℕ) * (3 : ℝ)^(k+1) * (2 : ℝ)^k
  have hD : 0 < D := by dsimp [D];positivity
  refine ⟨A*D,mul_pos hA hD,max G (k+3),?_⟩
  intro g hg Q hQ hkQ p hp hpsum s hs Y hY
  have hg2 : 2 ≤ g := by omega
  have hH : 2*Q ≤ complexity g 0 := by unfold complexity;omega
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0<g by omega)
  have hHR : 0 < (complexity g 0 : ℝ) := by exact_mod_cast (show 0<complexity g 0 by omega)
  have hgH : (g : ℝ) ≤ (complexity g 0 : ℝ) := by
    exact_mod_cast (show g ≤ complexity g 0 by unfold complexity;omega)
  have hDq : Real.sqrt (Q : ℝ)*(3 : ℝ)^Q*(2 : ℝ)^(Q-1) ≤ D := by
    have hroot : Real.sqrt (Q : ℝ) ≤ Real.sqrt (k+1 : ℕ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hkQ)
    have h3 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkQ
    have h2 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show Q-1≤k by omega)
    exact mul_le_mul (mul_le_mul hroot h3 (by positivity) (by positivity))
      h2 (by positivity) (by positivity)
  have hpow : (g : ℝ)^(Q-1) ≤ (complexity g 0 : ℝ)^(Q-1) :=
    pow_le_pow_left₀ hgR.le hgH _
  have hgamma := stable_genus_gamma_rate Q (complexity g 0) hQ hH p s
    (fun a ha => ⟨(hs a ha).1,(hs a ha).2.1⟩)
  have hgammap : 0 ≤
      (Real.sqrt (Q : ℝ)*(3 : ℝ)^Q*(2 : ℝ)^(Q-1)) := by positivity
  have hrate :
      (Real.sqrt (Q : ℝ)*(3 : ℝ)^Q*(2 : ℝ)^(Q-1)) /
        (complexity g 0 : ℝ)^(Q-1) ≤ D/(g : ℝ)^(Q-1) :=
    div_le_div₀ hD.le hDq (by positivity) hpow
  have hr : 0 ≤ A*(r Y)^k := mul_nonneg hA.le (pow_nonneg (r_pos Y hY).le _)
  calc
    _ = ∑ a ∈ s, (∏ i, markedF P (a i) (p i) (XR Y)) / markedF P g 0 (XR Y) := by
      rw [sum_div]
    _ ≤ ∑ a ∈ s, A*(r Y)^k*
        ((∏ i, gammaWeight (complexity (a i) (p i)))/gammaWeight (complexity g 0)) := by
      apply sum_le_sum
      intro a ha
      exact hprod g (le_of_max_le_left hg) Q hQ hkQ a p (hs a ha).1 hp hpsum
        (hs a ha).2.1 (hs a ha).2.2 Y hY
    _ = A*(r Y)^k*
        ((∑ a ∈ s, ∏ i, gammaWeight (complexity (a i) (p i)))/gammaWeight (complexity g 0)) := by
      rw [sum_div,mul_sum]
    _ ≤ A*(r Y)^k*(D/(g : ℝ)^(Q-1)) :=
      mul_le_mul_of_nonneg_left (hgamma.trans hrate) hr
    _ = _ := by ring

end WP.TightSeparating
