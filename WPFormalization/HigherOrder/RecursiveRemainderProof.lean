import WPFormalization.HigherOrder.GlobalScalarRemainderRows
import WPFormalization.HigherOrder.GlobalProfileRemainder
import WPFormalization.HigherOrder.FourStageInduction
/-! The actual all-order remainder assertion of C.19.
All four genuine recursion stages and the complete first-order base are supplied
before the positive strong induction is applied. The conclusion is exactly the
frozen UniformRecursiveRemainderTarget, with no extra induction or path premise.
The full C.3 proposition still has a separate finite-data obligation. -/

noncomputable section
namespace WP.HigherOrder

lemma scalar_row_budget_mono (d b D B X : ℝ) (_hd : 0 ≤ d) (hb : 0 ≤ b)
    (hD : 0 ≤ D) (hdD : d ≤ D) (hbB : b ≤ B) (hX : 0 ≤ X)
    (L : ℕ) (e : ℕ → ℝ) (he : ∀ q, 0 ≤ e q) :
    d * (X + (∑ i ∈ Finset.Icc 1 L, b ^ i * e (L - i)) + b ^ L) ≤
      D * B ^ L + D * X + ∑ i ∈ Finset.Icc 1 L, D * B ^ i * e (L - i) := by
  have hsum : (∑ i ∈ Finset.Icc 1 L, b ^ i * e (L - i)) ≤
      ∑ i ∈ Finset.Icc 1 L, B ^ i * e (L - i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hbB _) (he _)
  have hsum0 : 0 ≤ ∑ i ∈ Finset.Icc 1 L, b ^ i * e (L - i) :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (pow_nonneg hb _) (he _))
  have hbase : X + (∑ i ∈ Finset.Icc 1 L, b ^ i * e (L - i)) + b ^ L ≤
      X + (∑ i ∈ Finset.Icc 1 L, B ^ i * e (L - i)) + B ^ L :=
    add_le_add (add_le_add le_rfl hsum) (pow_le_pow_left₀ hb hbB L)
  have hprod := mul_le_mul hdD hbase (add_nonneg (add_nonneg hX hsum0) (pow_nonneg hb L)) hD
  apply hprod.trans_eq
  simp only [mul_add, Finset.mul_sum, mul_assoc]
  ring

theorem canonical_uniform_recursive_remainders (P : PsiTheory) :
    UniformRecursiveRemainderTarget P := by
  obtain ⟨Dp, Bp, Mp, hDp, hBp1, hMp, hprow⟩ := global_profile_remainder_stage P
  have hBp : 0 < Bp := zero_lt_one.trans_le hBp1
  obtain ⟨Dc, Bc, Mc, hDc, hBc, hMc, hcrow⟩ := global_cusp_remainder_stage P
  obtain ⟨Dh, Bh, Mh, hDh, hBh, hMh, hhrow⟩ := global_high_genus_remainder_stage P
  obtain ⟨Dg, Bg, Mg, hDg, hBg, hMg, hgrow⟩ := global_one_genus_remainder_stage P
  obtain ⟨C₁, M₁, hC₁, hM₁, hfirst⟩ := canonical_first_order_stage_bounds P
  let M : ℕ := Mp + Mc + Mh + Mg + M₁
  have hpM : Mp ≤ M := by dsimp [M]; omega
  have hcM : Mc ≤ M := by dsimp [M]; omega
  have hhM : Mh ≤ M := by dsimp [M]; omega
  have hgM : Mg ≤ M := by dsimp [M]; omega
  have h₁M : M₁ ≤ M := by dsimp [M]; omega
  have hM2 : 2 ≤ M := hMp.trans hpM
  let D : ℝ := Dp + Dc + Dh + Dg + 1
  let B : ℝ := Bp + Bc + Bh + Bg + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hpD : Dp ≤ D := by dsimp [D]; linarith
  have hcD : Dc ≤ D := by dsimp [D]; linarith
  have hhD : Dh ≤ D := by dsimp [D]; linarith
  have hgD : Dg ≤ D := by dsimp [D]; linarith
  have hpB : Bp ≤ B := by dsimp [B]; linarith
  have hcB : Bc ≤ B := by dsimp [B]; linarith
  have hhB : Bh ≤ B := by dsimp [B]; linarith
  have hgB : Bg ≤ B := by dsimp [B]; linarith
  let U : Fin 4 → ℕ → ℝ → Prop := RemainderStageBound P M
  have hmono : ∀ s n, Monotone (U s n) := remainderStageBound_mono P M
  have hbase : ∀ s, U s 1 C₁ := hfirst M h₁M
  have hP : ∀ n : ℕ, 2 ≤ n → ∀ e : ℕ → ℝ, (∀ m, 0 ≤ e m) →
      (∀ m : ℕ, 1 ≤ m → m < n → ∀ s, U s m (e m)) →
      U 0 n (D * B ^ n + ∑ i ∈ Finset.Icc 1 n, D * B ^ i * e (n - i)) := by
    intro n hn e he hprev
    have hp := hprow M hpM n hn e he hprev
    apply hmono 0 n _ hp
    simpa only [zero_add, mul_zero, add_zero] using
      scalar_row_budget_mono Dp Bp D B 0 hDp.le hBp.le hD.le hpD hpB (by norm_num) n e he
  have hC : ∀ n : ℕ, 2 ≤ n → ∀ E : ℝ, 0 ≤ E → U 0 n E →
      U 1 n (D * B ^ n + D * E) := by
    intro n hn E hE hU
    have hc := hcrow M hcM n (by omega) E hE hU
    apply hmono 1 n _ hc
    simpa only [mul_zero, Finset.sum_const_zero, add_zero] using
      scalar_row_budget_mono Dc Bc D B E hDc.le hBc.le hD.le hcD hcB hE n (fun _ => 0) (fun _ => le_rfl)
  have hH : ∀ n : ℕ, 2 ≤ n → ∀ e : ℕ → ℝ, (∀ m, 0 ≤ e m) →
      (∀ m : ℕ, 1 ≤ m → m < n → ∀ s, U s m (e m)) →
      ∀ E : ℝ, 0 ≤ E → U 0 n E →
      U 2 n (D * B ^ n + D * E + ∑ i ∈ Finset.Icc 1 n, D * B ^ i * e (n - i)) := by
    intro n hn e he hprev E hE hU
    have hh := hhrow M hhM n (by omega) e he hprev E hE hU
    exact hmono 2 n (scalar_row_budget_mono Dh Bh D B E hDh.le hBh.le hD.le hhD hhB hE n e he) hh
  have hG : ∀ n : ℕ, 2 ≤ n → ∀ e : ℕ → ℝ, (∀ m, 0 ≤ e m) →
      (∀ m : ℕ, 1 ≤ m → m < n → ∀ s, U s m (e m)) →
      ∀ C H : ℝ, 0 ≤ C → 0 ≤ H → U 1 n C → U 2 n H →
      U 3 n (D * B ^ n + D * (H + C) + ∑ i ∈ Finset.Icc 1 n, D * B ^ i * e (n - i)) := by
    intro n hn e he hprev C H hC hH hUc hUh
    have hg := hgrow M hgM n (by omega) e he hprev C H hC hH hUc hUh
    exact hmono 3 n (scalar_row_budget_mono Dg Bg D B (H + C) hDg.le hBg.le hD.le hgD hgB
      (add_nonneg hH hC) n e he) hg
  obtain ⟨C, Q, hC, hQ, hbound⟩ := four_stage_predicate_geometric_closure U D D B D C₁
    hD.le hD.le hB hD.le hC₁.le hmono hbase hP hC hH hG
  exact uniformRecursiveRemainderTarget_of_stage_bounds P C Q M hC hQ hM2 hbound
end WP.HigherOrder
