import WPFormalization.Analysis.SeparatingRemainderTools
import WPFormalization.Marked.SeparatingProof
import WPFormalization.Marked.SingleMarkingProfile

/-! The actual all-zero separating mass after both orientations of complexity loss two have been removed. All marking counts, including one, have a uniform cubic remainder. -/

noncomputable section
open Set
open scoped BigOperators
namespace WP

def markedSplitRemainderGenus (P : PsiTheory) (g p c j : ℕ) (Y : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (p-c+1), if 3 ≤ 2*j+s ∧ 3 ≤ 2*(g-j)+(p-c-s) then
    markedSplitTerm P g p c j s Y else 0

def markedSplitRemainder (P : PsiTheory) (g p c : ℕ) (Y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (g+1), markedSplitRemainderGenus P g p c j Y

lemma markedSplitTerm_nonneg (P : PsiTheory) (g p c j s : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (hs : s ≤ p-c) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ markedSplitTerm P g p c j s Y := by
  have hq₁ : 1 ≤ s+c := by rcases hc with rfl|rfl <;> omega
  have hq₂ : 1 ≤ p-s := by rcases hc with rfl|rfl <;> omega
  unfold markedSplitTerm
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (W_nonneg P j (s+c) hq₁ Y hY)) (W_nonneg P (g-j) (p-s) hq₂ Y hY))
      (W_pos P g p (by omega) (by unfold Stable;omega) Y hY).le

lemma markedSplitRemainderGenus_nonneg (P : PsiTheory) (g p c j : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ markedSplitRemainderGenus P g p c j Y := by
  apply Finset.sum_nonneg
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  split_ifs
  · exact markedSplitTerm_nonneg P g p c j s hg hp hc (by omega) Y hY
  · exact le_rfl

lemma markedSplitRemainderGenus_le (P : PsiTheory) (g p c j : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    markedSplitRemainderGenus P g p c j Y ≤ markedSplitGenus P g p c j Y := by
  apply Finset.sum_le_sum
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  split_ifs
  · exact le_rfl
  · exact markedSplitTerm_nonneg P g p c j s hg hp hc (by omega) Y hY

lemma markedSplitRemainderGenus_symm (P : PsiTheory) (g p c j : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) (hj : j ≤ g) (Y : ℝ) :
    markedSplitRemainderGenus P g p c (g-j) Y = markedSplitRemainderGenus P g p c j Y := by
  unfold markedSplitRemainderGenus
  rw [←Finset.sum_range_reflect (fun s => if 3 ≤ 2*(g-j)+s ∧
    3 ≤ 2*(g-(g-j))+(p-c-s) then markedSplitTerm P g p c (g-j) s Y else 0) (p-c+1)]
  apply Finset.sum_congr rfl
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  have hsQ : s ≤ p-c := by omega
  have hcP : c ≤ p := by rcases hc with rfl|rfl <;> omega
  have h1 : (p-c)-s+c=p-s := by omega
  have h2 : p-((p-c)-s)=s+c := by omega
  have h3 : g-(g-j)=j := by omega
  have h4 : (p-c)-((p-c)-s)=s := by omega
  simp only [Nat.add_sub_cancel,h3,h4]
  by_cases H : 3 ≤ 2*j+s ∧ 3 ≤ 2*(g-j)+(p-c-s)
  · simp only [if_pos H,if_pos (And.symm H)]
    unfold markedSplitTerm
    rw [h1,h2,h3,Nat.choose_symm hsQ]
    ring
  · simp only [if_neg H,if_neg (show ¬(3 ≤ 2*(g-j)+(p-c-s) ∧ 3 ≤ 2*j+s) by tauto)]

lemma markedSplitRemainder_half_bound (P : PsiTheory) (g p c N : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (hN : 2 ≤ N) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    markedSplitRemainder P g p c Y ≤ 2*(markedSplitRemainderGenus P g p c 0 Y+
      (∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then markedSplitRemainderGenus P g p c j Y else 0)+
      markedSplitMacroscopic P g p c N Y) := by
  have hb := Analysis.finite_symmetric_sum_le_twice_half g
    (fun j => markedSplitRemainderGenus P g p c j Y)
    (fun j _ => markedSplitRemainderGenus_nonneg P g p c j hg hp hc Y hY)
    (fun j hj => markedSplitRemainderGenus_symm P g p c j hp hc hj Y)
  rw [Analysis.finite_half_cut_partition g N hN] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num))
  unfold markedSplitMacroscopic
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · exact markedSplitRemainderGenus_le P g p c j hg hp hc Y hY
  · exact le_rfl

end WP
namespace WP
lemma markedSplitRemainder_low_genus_bound (P : PsiTheory) (p c : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, 2 ≤ G ∧ ∀ g ≥ G, ∀ j ≤ 1, ∀ Y ∈ Icc (0:ℝ) y₀,
      markedSplitRemainderGenus P g p c j Y ≤ C/(g:ℝ)^3 := by
  obtain ⟨Cr,hCr,hratio⟩ := W_small_genus_ratio_uniform
  obtain ⟨D,hD,hW⟩ := W_finite_marking_factorial_bound P (p+1)
  let H : ℝ := D^2*((p+3).factorial:ℝ)
  let C : ℝ := (2:ℝ)^(p-c)*H*Cr^3
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hH : 0<H := by dsimp [H];positivity
  obtain ⟨G,hG⟩ := exists_nat_gt (Cr+2)
  have hG2 : 2 ≤ G := by exact_mod_cast (show (2:ℝ) ≤ G by linarith)
  refine ⟨C,by dsimp [C];positivity,G,hG2,?_⟩
  intro g hg j hj Y hY
  have hg2 : 2 ≤ g := hG2.trans hg
  have hgR : (G:ℝ) ≤ g := by exact_mod_cast hg
  have hgp : 0<(g:ℝ) := by exact_mod_cast (show 0<g by omega)
  let x : ℝ := Cr/(g:ℝ)
  have hx : 0 ≤ x := by dsimp [x];positivity
  have hx1 : x ≤ 1 := by dsimp [x];apply (div_le_one hgp).2;linarith
  have hchoose : (∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ))=(2:ℝ)^(p-c) := by
    exact_mod_cast Nat.sum_range_choose (p-c)
  calc
    _ ≤ ∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ)*(H*x^3) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs0 := Finset.mem_range.mp hs
      have hsp : s<p := by rcases hc with rfl|rfl <;> omega
      have hq1 : 1 ≤ s+c := by rcases hc with rfl|rfl <;> omega
      have hqM : s+c ≤ p+1 := by rcases hc with rfl|rfl <;> omega
      by_cases hmask : 3 ≤ 2*j+s ∧ 3 ≤ 2*(g-j)+(p-c-s)
      · simp only [if_pos hmask]
        have hr := hratio P g p j s hg2 hp (by omega) hsp Y hY
        change W P (g-j) (p-s) Y/W P g p Y ≤ x^(2*j+s) at hr
        have hr' : W P (g-j) (p-s) Y/W P g p Y ≤ x^3 :=
          hr.trans (pow_le_pow_of_le_one hx hx1 hmask.1)
        have hw := hW (s+c) hq1 hqM j Y hY
        have hDb : D^(j+1) ≤ D^2 := pow_le_pow_right₀ hD (by omega)
        have hFb : ((2*j+(p+1)).factorial:ℝ) ≤ ((p+3).factorial:ℝ) := by
          exact_mod_cast Nat.factorial_le (show 2*j+(p+1) ≤ p+3 by omega)
        have hw' : W P j (s+c) Y ≤ H := hw.trans (by
          dsimp [H]
          exact mul_le_mul hDb hFb (by positivity) (by positivity))
        have hw0 := W_nonneg P j (s+c) hq1 Y hY
        have hb : W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y ≤ H*x^3 := by
          calc
            _ = W P j (s+c) Y*(W P (g-j) (p-s) Y/W P g p Y) := by ring
            _ ≤ W P j (s+c) Y*x^3 := mul_le_mul_of_nonneg_left hr' hw0
            _ ≤ H*x^3 := mul_le_mul_of_nonneg_right hw' (pow_nonneg hx _)
        simpa only [markedSplitTerm,mul_assoc,div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Nat.choose (p-c) s))
      · simp only [if_neg hmask]
        positivity
    _ = _ := by rw [←Finset.sum_mul,hchoose];dsimp [C,x];rw [div_pow];ring
end WP
namespace WP
lemma markedSplitMacroscopic_power_bound (P : PsiTheory) (p c N q : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) (hN : 2 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      markedSplitMacroscopic P g p c N Y ≤ C/(g:ℝ)^q := by
  obtain ⟨C,α,hC,hα,G,hpoint⟩ := marked_split_macroscopic_decay P p c N hp hc hN
  refine ⟨(2:ℝ)^(p-c)*C*(2*((q+1).factorial:ℝ))/α^(q+1),by positivity,max G 1,?_⟩
  intro g hg Y hY
  have hgG : G ≤ g := (le_max_left _ _).trans hg
  have hg1 : 1 ≤ g := (le_max_right _ _).trans hg
  have hchoose : (∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ))=(2:ℝ)^(p-c) := by
    exact_mod_cast Nat.sum_range_choose (p-c)
  have hinner (j : ℕ) (hj : g/N < j ∧ 2*j ≤ g) :
      (∑ s ∈ Finset.range (p-c+1), markedSplitTerm P g p c j s Y) ≤
        (2:ℝ)^(p-c)*C*Real.exp (-α*(g:ℝ)) := by
    calc
      _ ≤ ∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ)*(C*Real.exp (-α*(g:ℝ))) := by
        apply Finset.sum_le_sum
        intro s hs
        have hp' := hpoint g hgG j hj.1 hj.2 s hs Y hY
        simpa only [markedSplitTerm,mul_assoc,div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg (Nat.choose (p-c) s))
      _ = _ := by rw [←Finset.sum_mul,hchoose];ring
  calc
    _ ≤ ∑ j ∈ Finset.range (g+1), (2:ℝ)^(p-c)*C*Real.exp (-α*(g:ℝ)) := by
      unfold markedSplitMacroscopic
      apply Finset.sum_le_sum
      intro j hj
      by_cases hi : g/N < j ∧ 2*j ≤ g
      · simp only [if_pos hi]
        exact hinner j hi
      · simp only [if_neg hi]
        positivity
    _ = (2:ℝ)^(p-c)*C*(((g:ℝ)+1)*Real.exp (-α*(g:ℝ))) := by simp;ring
    _ ≤ (2:ℝ)^(p-c)*C*((2*((q+1).factorial:ℝ))/(α^(q+1)*(g:ℝ)^q)) :=
      mul_le_mul_of_nonneg_left (Analysis.linear_times_exp_decay_power_bound α hα g q hg1) (by positivity)
    _ = _ := by ring

end WP
namespace WP
lemma markedSplit_small_genus_two_bound (P : PsiTheory) (p c : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ g ≥ N*(p+5), ∀ Y ∈ Icc (0:ℝ) y₀,
      (∑ j ∈ Finset.range (g/N+1), if 2 ≤ j then markedSplitGenus P g p c j Y else 0) ≤ C/(g:ℝ)^4 := by
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
  refine ⟨B*(2*((p+5).factorial:ℝ)*K^2),by positivity,N,hN2,?_⟩
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
  have htotal : (∑ j ∈ Finset.range (g/N+1), if 2 ≤ j then markedSplitGenus P g p c j Y else 0) ≤
      B*(∑ j ∈ Finset.range (g/N+1), if 2 ≤ j then
        ((2*j+(p+1)).factorial:ℝ)*(K/(g:ℝ)^2)^j else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hj1 : 2 ≤ j
    · simp only [if_pos hj1]
      exact hinner j hj (by omega)
    · simp [hj1]
  have htail := Analysis.factorial_geometric_tail_start_two (p+1) N g K hK.le hNpos hNK (by simpa [Nat.add_assoc] using hg)
  calc
    _ ≤ B*(∑ j ∈ Finset.range (g/N+1), if 2 ≤ j then
        ((2*j+(p+1)).factorial:ℝ)*(K/(g:ℝ)^2)^j else 0) := htotal
    _ ≤ B*((2*(((p+1)+4).factorial:ℝ)*K^2)/(g:ℝ)^4) := mul_le_mul_of_nonneg_left htail hB.le
    _ = _ := by
      have he : (p+1)+4=p+5 := by omega
      rw [he]
      ring

end WP
namespace WP
lemma markedSplitRemainder_bound (P : PsiTheory) (p c : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      markedSplitRemainder P g p c Y ≤ C/(g:ℝ)^3 := by
  obtain ⟨Cl,hCl,Gl,hGl,hlow⟩ := markedSplitRemainder_low_genus_bound P p c hp hc
  obtain ⟨Cs,hCs,N,hN,hsmall⟩ := markedSplit_small_genus_two_bound P p c hp hc
  obtain ⟨Cm,hCm,Gm,hmacro⟩ := markedSplitMacroscopic_power_bound P p c N 3 hp hc hN
  refine ⟨4*Cl+2*Cs+2*Cm,by positivity,max Gl (max (N*(p+5)) Gm),?_⟩
  intro g hg Y hY
  have hgL : Gl ≤ g := (le_max_left _ _).trans hg
  have hgS : N*(p+5) ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgM : Gm ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hg2 : 2 ≤ g := hGl.trans hgL
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
  have hgp : 0<(g:ℝ) := by linarith
  have hcut : 1 ≤ g/N := (Nat.le_div_iff_mul_le (show 0<N by omega)).2 (by nlinarith)
  have hs := hsmall g hgS Y hY
  have hs3 : (∑ j ∈ Finset.range (g/N+1), if 2 ≤ j then markedSplitGenus P g p c j Y else 0) ≤ Cs/(g:ℝ)^3 :=
    hs.trans (div_le_div_of_nonneg_left hCs.le (by positivity) (by nlinarith [sq_nonneg ((g:ℝ)-1)] : (g:ℝ)^3 ≤ (g:ℝ)^4))
  have hsmallRem : (∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then markedSplitRemainderGenus P g p c j Y else 0) ≤
      (Cl+Cs)/(g:ℝ)^3 := by
    calc
      _ ≤ ∑ j ∈ Finset.range (g/N+1), ((if j=1 then Cl/(g:ℝ)^3 else 0)+
          (if 2 ≤ j then markedSplitGenus P g p c j Y else 0)) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hj1 : j=1
        · subst j
          simp only [if_pos rfl,show 1 ≤ (1:ℕ) by omega,if_true,show ¬2 ≤ (1:ℕ) by omega,if_false,add_zero]
          exact hlow g hgL 1 le_rfl Y hY
        · by_cases hj2 : 2 ≤ j
          · have hj0 : 1 ≤ j := by omega
            simp only [if_neg hj1,if_pos hj2,if_pos hj0,zero_add]
            exact markedSplitRemainderGenus_le P g p c j hg2 hp hc Y hY
          · have hj0 : ¬1 ≤ j := by omega
            simp only [if_neg hj1,if_neg hj2,if_neg hj0,zero_add]
            exact le_rfl
      _ = Cl/(g:ℝ)^3+(∑ j ∈ Finset.range (g/N+1), if 2 ≤ j then markedSplitGenus P g p c j Y else 0) := by
        rw [Finset.sum_add_distrib]
        simp [show 1<g/N+1 by omega]
      _ ≤ Cl/(g:ℝ)^3+Cs/(g:ℝ)^3 := add_le_add le_rfl hs3
      _ = _ := by ring
  have hb := markedSplitRemainder_half_bound P g p c N hg2 hp hc hN Y hY
  calc
    _ ≤ 2*(markedSplitRemainderGenus P g p c 0 Y+
      (∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then markedSplitRemainderGenus P g p c j Y else 0)+
      markedSplitMacroscopic P g p c N Y) := hb
    _ ≤ 2*(Cl/(g:ℝ)^3+(Cl+Cs)/(g:ℝ)^3+Cm/(g:ℝ)^3) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add (hlow g hgL 0 (by omega) Y hY) hsmallRem)
        (hmacro g hgM Y hY)) (by norm_num)
    _ = _ := by ring
end WP
namespace WP
lemma markedSplitRemainder_one_bound (P : PsiTheory) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      markedSplitRemainder P g 1 1 Y ≤ C/(g:ℝ)^3 := by
  obtain ⟨Cr,hCr,hcusp⟩ := W_cusp_uniform_bound
  obtain ⟨Ci,hCi,Gi,hInv⟩ := W_one_cusp_inverse_uniform P
  obtain ⟨Ct,hCt,Gt,hT⟩ := markedSplitRemainder_bound P 2 2 (by omega) (Or.inr rfl)
  refine ⟨2*Cr^2*Ci*Ct,by positivity,max 2 (max Gi Gt),?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgi : Gi ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgt : Gt ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hW1 : 0<W P g 1 Y := W_pos P g 1 (by omega) (by unfold Stable;omega) Y hY
  have hW2 : 0<W P g 2 Y := W_pos P g 2 (by omega) (by unfold Stable;omega) Y hY
  let mask (j : ℕ) : Prop := 3 ≤ 2*j ∧ 3 ≤ 2*(g-j)
  let A₁ : ℝ := ∑ j ∈ Finset.range (g+1), if mask j then W P j 1 Y*W P (g-j) 1 Y else 0
  let A₂ : ℝ := ∑ j ∈ Finset.range (g+1), if mask j then W P j 2 Y*W P (g-j) 2 Y else 0
  have hs : markedSplitRemainder P g 1 1 Y=A₁/W P g 1 Y := by
    simp only [markedSplitRemainder,markedSplitRemainderGenus,markedSplitTerm,
      Nat.reduceSub,Nat.zero_add,Nat.sub_zero,Nat.add_zero,Finset.sum_range_one,
      Nat.choose_zero_right,Nat.cast_one,one_mul]
    dsimp [A₁,mask]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  have ht : markedSplitRemainder P g 2 2 Y=A₂/W P g 2 Y := by
    simp only [markedSplitRemainder,markedSplitRemainderGenus,markedSplitTerm,
      Nat.reduceSub,Nat.zero_add,Nat.sub_zero,Nat.add_zero,Finset.sum_range_one,
      Nat.choose_zero_right,Nat.cast_one,one_mul]
    dsimp [A₂,mask]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  have hb : A₂ ≤ (Ci*Ct/(g:ℝ)^2)*W P g 1 Y := by
    have hTbound := hT g hgt Y hY
    rw [ht] at hTbound
    have hsum := (div_le_iff₀ hW2).mp hTbound
    calc
      _ ≤ (Ct/(g:ℝ)^3)*W P g 2 Y := hsum
      _ ≤ (Ct/(g:ℝ)^3)*(Ci*(g:ℝ)*W P g 1 Y) :=
        mul_le_mul_of_nonneg_left (hInv g hgi Y hY) (by positivity)
      _ = _ := by field_simp
  have hsum : (g:ℝ)*A₁ ≤ (2*Cr^2)*A₂ := by
    dsimp [A₁,A₂]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hm : mask j
    · simp only [if_pos hm]
      exact separatingS_one_term_bound Cr hCr.le hcusp P g j hg2
        (by have := Finset.mem_range.mp hj;omega) Y hY
    · simp only [if_neg hm,mul_zero]
      exact le_rfl
  rw [hs]
  apply (div_le_div_iff₀ hW1 (by positivity : (0:ℝ)<(g:ℝ)^3)).2
  have hh := mul_le_mul_of_nonneg_right hsum (sq_nonneg (g:ℝ))
  calc
    _ = ((g:ℝ)*A₁)*(g:ℝ)^2 := by ring
    _ ≤ ((2*Cr^2)*A₂)*(g:ℝ)^2 := hh
    _ ≤ ((2*Cr^2)*((Ci*Ct/(g:ℝ)^2)*W P g 1 Y))*(g:ℝ)^2 := by
      gcongr
    _ = _ := by field_simp
end WP
namespace WP
lemma markedSplitRemainder_all_markings_bound (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      markedSplitRemainder P g p 1 Y ≤ C/(g:ℝ)^3 := by
  by_cases h : p=1
  · subst p
    exact markedSplitRemainder_one_bound P
  · exact markedSplitRemainder_bound P p 1 (by omega) (Or.inl rfl)
end WP
