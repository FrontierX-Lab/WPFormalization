import WPFormalization.Marked.FiniteFamilies
import WPFormalization.Marked.SeparatingDefinitions
import WPFormalization.Analysis.FactorialTail

/-! Actual finite estimates for the separating terms of Section 6. The
proofs use the original marked W functions and the already proved ratio
and growth bounds; no separating estimate is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace WP

lemma markedSplitSmallPositive_bound (P : PsiTheory) (p c : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ g ≥ N*(p+5), ∀ Y ∈ Icc (0:ℝ) y₀,
      markedSplitSmallPositive P g p c N Y ≤ C/(g:ℝ)^2 := by
  obtain ⟨Cr,hCr,hratio⟩ := W_small_genus_ratio_uniform
  obtain ⟨D,hD,hW⟩ := W_finite_marking_factorial_bound P (p+1)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let V : ℝ := (max 1 Cr)^p
  let K : ℝ := D*Cr^2
  let B : ℝ := (2:ℝ)^(p-c)*D*V
  have hV : 0 < V := by dsimp [V];positivity
  have hK : 0 < K := by dsimp [K];positivity
  have hB : 0 < B := by dsimp [B];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (18*K+2)
  have hN2 : 2 ≤ N := by exact_mod_cast (show (2:ℝ) ≤ N by linarith)
  have hNpos : 0 < N := by omega
  have hNK : 18*K ≤ (N:ℝ)^2 := by
    have hNr : (1:ℝ) ≤ N := by exact_mod_cast (show 1≤N by omega)
    nlinarith [mul_nonneg (show 0≤(N:ℝ) by positivity) (show 0≤(N:ℝ)-1 by linarith)]
  refine ⟨B*(2*((p+3).factorial:ℝ)*K),by positivity,N,hN2,?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := by nlinarith
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast (show 1≤g by omega)
  have hgpos : 0 < (g:ℝ) := lt_of_lt_of_le zero_lt_one hgR
  let x : ℝ := Cr/(g:ℝ)
  have hx : 0 ≤ x := by dsimp [x];positivity
  have hxmax : x ≤ max 1 Cr := by
    dsimp [x]
    exact (div_le_self hCr.le hgR).trans (le_max_right _ _)
  have hxs (s : ℕ) (hs : s < p) : x^s ≤ V :=
    (pow_le_pow_left₀ hx hxmax s).trans (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  have hbase : D*x^2=K/(g:ℝ)^2 := by dsimp [x,K];rw [div_pow];ring
  have hchoose : (∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ))=(2:ℝ)^(p-c) := by
    exact_mod_cast Nat.sum_range_choose (p-c)
  have hinner (j : ℕ) (hj : j ∈ Finset.range (g/N+1)) (hj1 : 1 ≤ j) :
      (∑ s ∈ Finset.range (p-c+1), markedSplitTerm P g p c j s Y) ≤
      B*(((2*j+(p+1)).factorial:ℝ)*(K/(g:ℝ)^2)^j) := by
    have hjN : j ≤ g/N := by have := Finset.mem_range.mp hj;omega
    have hNj : j*N ≤ g := (Nat.le_div_iff_mul_le hNpos).mp hjN
    have hjhalf : 2*j ≤ g := by nlinarith
    calc
      _ ≤ ∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ)*
          (D*V*(((2*j+(p+1)).factorial:ℝ)*(K/(g:ℝ)^2)^j)) := by
        apply Finset.sum_le_sum
        intro s hs
        have hs0 := Finset.mem_range.mp hs
        have hsp : s < p := by rcases hc with rfl|rfl <;> omega
        have hq1 : 1 ≤ s+c := by rcases hc with rfl|rfl <;> omega
        have hqM : s+c ≤ p+1 := by rcases hc with rfl|rfl <;> omega
        have hw := hW (s+c) hq1 hqM j Y hY
        have hrat := hratio P g p j s hg2 hp hjhalf hsp Y hY
        change W P (g-j) (p-s) Y / W P g p Y ≤ x^(2*j+s) at hrat
        have hw0 := W_nonneg P j (s+c) hq1 Y hY
        have hb : W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y ≤
            D*V*(((2*j+(p+1)).factorial:ℝ)*(K/(g:ℝ)^2)^j) := by
          calc
            _ = W P j (s+c) Y*(W P (g-j) (p-s) Y/W P g p Y) := by ring
            _ ≤ W P j (s+c) Y*x^(2*j+s) := mul_le_mul_of_nonneg_left hrat hw0
            _ ≤ (D^(j+1)*((2*j+(p+1)).factorial:ℝ))*x^(2*j+s) :=
              mul_le_mul_of_nonneg_right hw (pow_nonneg hx _)
            _ = (D*(((2*j+(p+1)).factorial:ℝ)*(K/(g:ℝ)^2)^j))*x^s := by
              rw [←hbase,mul_pow,pow_succ,pow_add,pow_mul]
              ring
            _ ≤ (D*(((2*j+(p+1)).factorial:ℝ)*(K/(g:ℝ)^2)^j))*V :=
              mul_le_mul_of_nonneg_left (hxs s hsp) (by positivity)
            _ = _ := by ring
        exact (by
          simpa only [markedSplitTerm,mul_assoc,div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Nat.choose (p-c) s)))
      _ = _ := by rw [←Finset.sum_mul,hchoose];dsimp [B];ring
  have htotal : markedSplitSmallPositive P g p c N Y ≤
      B*(∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then
        ((2*j+(p+1)).factorial:ℝ)*(K/(g:ℝ)^2)^j else 0) := by
    unfold markedSplitSmallPositive
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hj1 : 1 ≤ j
    · simp only [if_pos hj1]
      exact hinner j hj hj1
    · simp [hj1]
  have htail := Analysis.factorial_geometric_tail_bound (p+1) N g K hK.le hNpos hNK (by simpa [Nat.add_assoc] using hg)
  calc
    _ ≤ B*(∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then
        ((2*j+(p+1)).factorial:ℝ)*(K/(g:ℝ)^2)^j else 0) := htotal
    _ ≤ B*((2*(((p+1)+2).factorial:ℝ)*K)/(g:ℝ)^2) := mul_le_mul_of_nonneg_left htail hB.le
    _ = _ := by
      have he : (p+1)+2=p+3 := by omega
      rw [he]
      ring

lemma markedSplit_genus_zero_bound (P : PsiTheory) (p c : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, 2 ≤ G ∧ ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      (∑ s ∈ Finset.range (p-c+1), markedSplitTerm P g p c 0 s Y) ≤ C/(g:ℝ)^(3-c) := by
  obtain ⟨Cr,hCr,hratio⟩ := W_small_genus_ratio_uniform
  obtain ⟨D,hD,hW⟩ := W_finite_marking_factorial_bound P (p+1)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let C : ℝ := (2:ℝ)^(p-c)*D*((p+1).factorial:ℝ)*Cr^(3-c)
  obtain ⟨G,hG⟩ := exists_nat_gt (Cr+2)
  have hG2 : 2 ≤ G := by exact_mod_cast (show (2:ℝ) ≤ G by linarith)
  refine ⟨C,by dsimp [C];positivity,G,hG2,?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := hG2.trans hg
  have hgR : (G:ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : 0 < (g:ℝ) := by exact_mod_cast (show 0<g by omega)
  let x : ℝ := Cr/(g:ℝ)
  have hx : 0 ≤ x := by dsimp [x];positivity
  have hx1 : x ≤ 1 := by dsimp [x];apply (div_le_one hgpos).2;linarith
  have hchoose : (∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ))=(2:ℝ)^(p-c) := by
    exact_mod_cast Nat.sum_range_choose (p-c)
  calc
    _ ≤ ∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ)*
        (D*((p+1).factorial:ℝ)*x^(3-c)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs0 := Finset.mem_range.mp hs
      have hsp : s < p := by rcases hc with rfl|rfl <;> omega
      have hq1 : 1 ≤ s+c := by rcases hc with rfl|rfl <;> omega
      have hqM : s+c ≤ p+1 := by rcases hc with rfl|rfl <;> omega
      by_cases hst : Stable 0 (s+c)
      · have hsc : 3-c ≤ s := by unfold Stable at hst;rcases hc with rfl|rfl <;> omega
        have hr := hratio P g p 0 s hg2 hp (by omega) hsp Y hY
        have hr' : W P g (p-s) Y/W P g p Y ≤ x^(3-c) := by
          simp only [Nat.sub_zero,Nat.mul_zero,Nat.zero_add] at hr
          exact hr.trans (pow_le_pow_of_le_one hx hx1 hsc)
        have hw := hW (s+c) hq1 hqM 0 Y hY
        norm_num only [Nat.zero_add,Nat.mul_zero,pow_one] at hw
        have hw0 := W_nonneg P 0 (s+c) hq1 Y hY
        have hb : W P 0 (s+c) Y*W P g (p-s) Y/W P g p Y ≤
            D*((p+1).factorial:ℝ)*x^(3-c) := by
          calc
            _ = W P 0 (s+c) Y*(W P g (p-s) Y/W P g p Y) := by ring
            _ ≤ W P 0 (s+c) Y*x^(3-c) := mul_le_mul_of_nonneg_left hr' hw0
            _ ≤ _ := mul_le_mul_of_nonneg_right hw (pow_nonneg hx _)
        simpa only [markedSplitTerm,Nat.sub_zero,mul_assoc,div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Nat.choose (p-c) s))
      · simp only [markedSplitTerm,W_unstable P 0 (s+c) hst Y,mul_zero,zero_mul,zero_div]
        positivity
    _ = _ := by
      rw [←Finset.sum_mul,hchoose]
      dsimp [C,x]
      rw [div_pow]
      ring

end WP
