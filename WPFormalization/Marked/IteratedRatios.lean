import WPFormalization.Marked.Positivity
/-! Iteration of the genuine cusp and genus-exchange inequalities. The final
cross-genus ratio is the actual estimate (6.12), including the single-marking
case that first passes through two markings. Its constant is uniform in the
parameter and in the distinguished marking count. -/
noncomputable section
open Set
namespace WP

lemma W_cusp_power_bound (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ P : PsiTheory, ∀ g p : ℕ, Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      (complexity g p:ℝ)*W P g p Y ≤ C*W P g (p+1) Y)
    (P : PsiTheory) (g p n : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (a : ℝ) (ha : 0 ≤ a) (hab : a ≤ (complexity g p:ℝ))
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    a^n*W P g p Y ≤ C^n*W P g (p+n) Y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs' : Stable g (p+n) := by unfold Stable at *;omega
    have hh : complexity g p ≤ complexity g (p+n) := by unfold complexity;omega
    have hhR : (complexity g p:ℝ) ≤ complexity g (p+n) := by exact_mod_cast hh
    have hnorm := W_nonneg P g (p+n) (by omega) Y hY
    have hnext : a*W P g (p+n) Y ≤ C*W P g ((p+n)+1) Y := by
      exact (mul_le_mul_of_nonneg_right (hab.trans hhR) hnorm).trans (hstep P g (p+n) hs' Y hY)
    calc
      _ = a*(a^n*W P g p Y) := by rw [pow_succ];ring
      _ ≤ a*(C^n*W P g (p+n) Y) := mul_le_mul_of_nonneg_left ih ha
      _ = C^n*(a*W P g (p+n) Y) := by ring
      _ ≤ C^n*(C*W P g ((p+n)+1) Y) := mul_le_mul_of_nonneg_left hnext (pow_nonneg hC _)
      _ = _ := by rw [pow_succ];simp only [Nat.add_assoc];ring

lemma W_genus_exchange_iterated (P : PsiTheory) (g p j : ℕ) (hj : j ≤ g)
    (hp : 2 ≤ p) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    W P (g-j) (p+2*j) Y ≤ W P g p Y := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hgj : 1 ≤ g-j := by omega
    have hi := W_genus_exchange_le P (g-j) (p+2*j) hgj (by omega) Y hY
    have h1 : g-j-1=g-(j+1) := by omega
    have h2 : p+2*j+2=p+2*(j+1) := by omega
    rw [h1,h2] at hi
    exact hi.trans (ih (by omega))
end WP
namespace WP
lemma W_small_genus_power_bound (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ P : PsiTheory, ∀ g p : ℕ, Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      (complexity g p:ℝ)*W P g p Y ≤ C*W P g (p+1) Y)
    (P : PsiTheory) (g p j s : ℕ) (hg : 2 ≤ g) (hp : 2 ≤ p)
    (hj : 2*j ≤ g) (hs : s < p) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    ((g:ℝ)/2)^(2*j+s) * W P (g-j) (p-s) Y ≤
      C^(2*j+s)*W P g p Y := by
  let a : ℝ := (g:ℝ)/2
  have ha : 0 ≤ a := by dsimp [a];positivity
  have hG : 1 ≤ g-j := by omega
  have hbase (q : ℕ) (hq : 1 ≤ q) : a ≤ (complexity (g-j) q:ℝ) := by
    have hh : g ≤ 2*complexity (g-j) q := by unfold complexity;omega
    have hhR : (g:ℝ) ≤ 2*(complexity (g-j) q:ℝ) := by exact_mod_cast hh
    dsimp [a]
    linarith
  have hq : 1 ≤ p-s := by omega
  by_cases hq2 : 2 ≤ p-s
  · have hst : Stable (g-j) (p-s) := by unfold Stable;omega
    have hc := W_cusp_power_bound C hC hstep P (g-j) (p-s) (2*j+s) hq hst a ha (hbase _ hq) Y hY
    have hlen : (p-s)+(2*j+s)=p+2*j := by omega
    rw [hlen] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left
      (W_genus_exchange_iterated P g p j (by omega) hp Y hY) (pow_nonneg hC _))
  · have heq : p-s=1 := by omega
    have hs1 : 1 ≤ s := by omega
    have hc1 := W_cusp_power_bound C hC hstep P (g-j) 1 (2*j+1) (by omega)
      (by unfold Stable;omega) a ha (hbase 1 (by omega)) Y hY
    have hlen1 : 1+(2*j+1)=2+2*j := by omega
    rw [hlen1] at hc1
    have hgen := W_genus_exchange_iterated P g 2 j (by omega) (by omega) Y hY
    have hc1' : a^(2*j+1)*W P (g-j) 1 Y ≤ C^(2*j+1)*W P g 2 Y :=
      hc1.trans (mul_le_mul_of_nonneg_left hgen (pow_nonneg hC _))
    have hst : Stable g 2 := by unfold Stable;omega
    have hbase2 : a ≤ (complexity g 2:ℝ) := by
      have hh : g ≤ 2*complexity g 2 := by unfold complexity;omega
      have hhR : (g:ℝ) ≤ 2*(complexity g 2:ℝ) := by exact_mod_cast hh
      dsimp [a]
      linarith
    have hc2 := W_cusp_power_bound C hC hstep P g 2 (s-1) (by omega) hst a ha hbase2 Y hY
    have hlen2 : 2+(s-1)=p := by omega
    rw [hlen2] at hc2
    have hn : (2*j+1)+(s-1)=2*j+s := by omega
    rw [heq]
    change a^(2*j+s)*W P (g-j) 1 Y ≤ _
    calc
      _ = a^(s-1)*(a^(2*j+1)*W P (g-j) 1 Y) := by rw [←hn,pow_add];ring
      _ ≤ a^(s-1)*(C^(2*j+1)*W P g 2 Y) := mul_le_mul_of_nonneg_left hc1' (pow_nonneg ha _)
      _ = C^(2*j+1)*(a^(s-1)*W P g 2 Y) := by ring
      _ ≤ C^(2*j+1)*(C^(s-1)*W P g p Y) := mul_le_mul_of_nonneg_left hc2 (pow_nonneg hC _)
      _ = _ := by rw [←hn,pow_add];ring

lemma W_small_genus_ratio_uniform : ∃ C : ℝ, 0 < C ∧ ∀ P : PsiTheory,
    ∀ g p j s : ℕ, 2 ≤ g → 2 ≤ p → 2*j ≤ g → s < p →
    ∀ Y ∈ Icc (0:ℝ) y₀,
      W P (g-j) (p-s) Y / W P g p Y ≤ (C/(g:ℝ))^(2*j+s) := by
  obtain ⟨C,hC,hstep⟩ := W_cusp_uniform_bound
  refine ⟨2*C,by positivity,?_⟩
  intro P g p j s hg hp hj hs Y hY
  have hb := W_small_genus_power_bound C hC.le hstep P g p j s hg hp hj hs Y hY
  have hden : 0 < W P g p Y := W_pos P g p (by omega) (by unfold Stable;omega) Y hY
  have hgR : 0 < (g:ℝ) := by exact_mod_cast (show 0<g by omega)
  have ha : 0 < ((g:ℝ)/2)^(2*j+s) := by positivity
  have he : W P (g-j) (p-s) Y / W P g p Y ≤ C^(2*j+s)/((g:ℝ)/2)^(2*j+s) := by
    apply (div_le_div_iff₀ hden ha).2
    nlinarith
  have hbase : C/((g:ℝ)/2)=(2*C)/(g:ℝ) := by field_simp
  rw [←div_pow,hbase] at he
  exact he
end WP
