import WPFormalization.Marked.LogGrowth
import WPFormalization.Marked.IteratedRatios

/-! Actual finite estimates for the separating terms of Section 6. The
proofs use the original marked W functions and the already proved ratio
and growth bounds; no separating estimate is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace WP

lemma W_unstable (P : PsiTheory) (g p : ℕ) (hs : ¬Stable g p) (Y : ℝ) : W P g p Y=0 := by
  unfold W
  rw [normalized_unstable P g (List.replicate p 0) Y (by simpa using hs),mul_zero]

lemma W_finite_marking_factorial_bound (P : PsiTheory) (M : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ q : ℕ, 1 ≤ q → q ≤ M → ∀ g : ℕ,
      ∀ Y ∈ Icc (0:ℝ) y₀, W P g q Y ≤ D^(g+1)*((2*g+M).factorial:ℝ) := by
  classical
  have hlocal (i : Fin M) := W_uniform_exponential_factorial P (i.val+1)
  choose C hC hb using hlocal
  let D := max 1 (∑ i : Fin M, C i)
  have hD : 1 ≤ D := le_max_left _ _
  have hCD (i : Fin M) : C i ≤ D :=
    (Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)).trans (le_max_right _ _)
  refine ⟨D,hD,?_⟩
  intro q hq hqM g Y hY
  by_cases hs : Stable g q
  · let i : Fin M := ⟨q-1,by omega⟩
    have hi : i.val+1=q := by dsimp [i];omega
    have hb' := hb i g (by rwa [hi]) Y hY
    rw [hi] at hb'
    exact hb'.trans (mul_le_mul
      (pow_le_pow_left₀ (hC i).le (hCD i) _)
      (by exact_mod_cast Nat.factorial_le (show 2*g+q ≤ 2*g+M by omega))
      (by positivity) (by positivity))
  · rw [W_unstable P g q hs Y]
    positivity

lemma W_uniform_log_growth_finite (P : PsiTheory) (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ G : ℕ, ∀ q : ℕ, 1 ≤ q → q ≤ M → ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |Real.log (W P g q Y)-Real.log (Real.Gamma (complexity g q))+
        (complexity g q:ℝ)*Real.log (A Y)| ≤ ε*(g:ℝ) := by
  classical
  have hlocal (i : Fin M) := W_uniform_log_growth P (i.val+1) (by omega) ε hε
  choose G hb using hlocal
  refine ⟨∑ i : Fin M, G i,?_⟩
  intro q hq hqM g hg Y hY
  let i : Fin M := ⟨q-1,by omega⟩
  have hi : i.val+1=q := by dsimp [i];omega
  have hGi : G i ≤ ∑ j : Fin M, G j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  simpa only [hi] using hb i g (hGi.trans hg) Y hY

lemma A_log_uniform_upper : ∃ B : ℝ, 0 ≤ B ∧ ∀ Y ∈ Icc (0:ℝ) y₀, Real.log (A Y) ≤ B := by
  have hc : Continuous (fun Y : Icc (0:ℝ) y₀ => A (Y:ℝ)) := by
    unfold A
    exact (Complex.continuous_re.comp (Analysis.barH_joint_continuous.comp
      (continuous_id.prodMk continuous_const))).div_const 3
  obtain ⟨M,hM⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  refine ⟨max 0 (Real.log (max M 1)),le_max_left _ _,?_⟩
  intro Y hY
  have hA : 0 < A Y := by
    unfold A
    exact div_pos (Analysis.barH_one_re_pos Y hY) (by norm_num)
  have hle : A Y ≤ max M 1 := (hM (mem_image_of_mem _
    (show (⟨Y,hY⟩:Icc (0:ℝ) y₀) ∈ (univ:Set (Icc (0:ℝ) y₀)) from mem_univ _))).trans (le_max_left _ _)
  exact (Real.log_le_log hA hle).trans (le_max_right _ _)

end WP
