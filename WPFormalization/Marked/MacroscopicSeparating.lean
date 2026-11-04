import WPFormalization.Marked.FiniteFamilies
import WPFormalization.Marked.SeparatingDefinitions
import WPFormalization.Analysis.SeparatingFiniteAlgebra

/-! Actual finite estimates for the separating terms of Section 6. The
proofs use the original marked W functions and the already proved ratio
and growth bounds; no separating estimate is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace WP

lemma marked_split_gamma_geometric (g p j s c : ℕ)
    (hg : 4 ≤ g) (hp : 2 ≤ p) (hj : 2 ≤ j) (hjhalf : 2*j ≤ g)
    (hs : s < p) (hc : c=1 ∨ c=2) :
    Real.Gamma (complexity j (s+c):ℝ)*Real.Gamma (complexity (g-j) (p-s):ℝ) /
      Real.Gamma (complexity g p:ℝ) ≤ (1/2:ℝ)^j := by
  apply Analysis.gamma_pair_ratio_le_geometric
  all_goals unfold complexity;rcases hc with rfl|rfl <;> omega

def markedLogError (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  Real.log (W P g p Y)-Real.log (Real.Gamma (complexity g p))+
    (complexity g p:ℝ)*Real.log (A Y)

lemma marked_split_log_ratio_upper (P : PsiTheory) (g p j s c : ℕ)
    (hg : 4 ≤ g) (hp : 2 ≤ p) (hj : 2 ≤ j) (hjhalf : 2*j ≤ g)
    (hs : s < p) (hc : c=1 ∨ c=2) (Y : ℝ) (hY : Y ∈ Icc 0 y₀)
    (B ε : ℝ) (hB : 0 ≤ B) (hA : Real.log (A Y) ≤ B)
    (he₁ : |markedLogError P j (s+c) Y| ≤ ε*(j:ℝ))
    (he₂ : |markedLogError P (g-j) (p-s) Y| ≤ ε*(g-j:ℕ))
    (he : |markedLogError P g p Y| ≤ ε*(g:ℝ)) :
    Real.log (W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y) ≤
      B-(j:ℝ)*Real.log 2+2*ε*(g:ℝ) := by
  have hc1 : 1 ≤ c := by rcases hc with rfl|rfl <;> omega
  have hW₁ := W_pos P j (s+c) (by omega) (by unfold Stable;omega) Y hY
  have hW₂ := W_pos P (g-j) (p-s) (by omega) (by unfold Stable;omega) Y hY
  have hW := W_pos P g p (by omega) (by unfold Stable;omega) Y hY
  have hΓ₁ : 0 < Real.Gamma (complexity j (s+c):ℝ) := Real.Gamma_pos_of_pos (by
    exact_mod_cast (show 0<complexity j (s+c) by unfold complexity;omega))
  have hΓ₂ : 0 < Real.Gamma (complexity (g-j) (p-s):ℝ) := Real.Gamma_pos_of_pos (by
    exact_mod_cast (show 0<complexity (g-j) (p-s) by unfold complexity;omega))
  have hΓ : 0 < Real.Gamma (complexity g p:ℝ) := Real.Gamma_pos_of_pos (by
    exact_mod_cast (show 0<complexity g p by unfold complexity;omega))
  have hGam := marked_split_gamma_geometric g p j s c hg hp hj hjhalf hs hc
  have hLogGam := Real.log_le_log (div_pos (mul_pos hΓ₁ hΓ₂) hΓ) hGam
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one]
    ring
  rw [Real.log_div (mul_ne_zero hΓ₁.ne' hΓ₂.ne') hΓ.ne',
    Real.log_mul hΓ₁.ne' hΓ₂.ne',Real.log_pow,hhalf] at hLogGam
  have hcomp : complexity j (s+c)+complexity (g-j) (p-s)+(2-c)=complexity g p := by
    rcases hc with rfl|rfl <;> unfold complexity <;> omega
  have hcompR : (complexity j (s+c):ℝ)+(complexity (g-j) (p-s):ℝ)+(2-c:ℕ)=(complexity g p:ℝ) := by
    exact_mod_cast hcomp
  have hdiff : (complexity g p:ℝ)-(complexity j (s+c):ℝ)-(complexity (g-j) (p-s):ℝ)=(2-c:ℕ) := by linarith
  have hA' : ((complexity g p:ℝ)-(complexity j (s+c):ℝ)-(complexity (g-j) (p-s):ℝ))*Real.log (A Y) ≤ B := by
    rw [hdiff]
    rcases hc with rfl|rfl
    · simpa using hA
    · simpa using hB
  have herr : ε*(j:ℝ)+ε*((g-j:ℕ):ℝ)+ε*(g:ℝ)=2*ε*(g:ℝ) := by
    rw [Nat.cast_sub (show j≤g by omega)]
    ring
  have he1 := (abs_le.mp he₁).2
  have he2 := (abs_le.mp he₂).2
  have hep := (abs_le.mp he).1
  unfold markedLogError at he1 he2 hep
  rw [Real.log_div (mul_ne_zero hW₁.ne' hW₂.ne') hW.ne',Real.log_mul hW₁.ne' hW₂.ne']
  nlinarith

lemma marked_split_macroscopic_decay (P : PsiTheory) (p c N : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) (hN : 2 ≤ N) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∃ G : ℕ,
      ∀ g ≥ G, ∀ j : ℕ, g/N < j → 2*j ≤ g →
      ∀ s ∈ Finset.range (p-c+1), ∀ Y ∈ Icc (0:ℝ) y₀,
        W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y ≤ C*Real.exp (-α*(g:ℝ)) := by
  have hNpos : 0 < N := by omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hNpos
  let α : ℝ := Real.log 2/(4*(N:ℝ))
  have hα : 0 < α := by dsimp [α];exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  obtain ⟨B,hB,hA⟩ := A_log_uniform_upper
  obtain ⟨H,hgrowth⟩ := W_uniform_log_growth_finite P (p+1) α hα
  refine ⟨Real.exp B,α,Real.exp_pos _,hα,N*(H+2)+2*H+4,?_⟩
  intro g hg j hj hjhalf s hs Y hY
  have hg4 : 4 ≤ g := by nlinarith
  have hcut : H+2 ≤ g/N := (Nat.le_div_iff_mul_le hNpos).2 (by nlinarith)
  have hjH : H ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hlargeH : H ≤ g-j := by omega
  have hgH : H ≤ g := by omega
  have hs0 := Finset.mem_range.mp hs
  have hsp : s < p := by rcases hc with rfl|rfl <;> omega
  have hq₁ : 1 ≤ s+c := by rcases hc with rfl|rfl <;> omega
  have hqM₁ : s+c ≤ p+1 := by rcases hc with rfl|rfl <;> omega
  have hq₂ : 1 ≤ p-s := by omega
  have he₁ : |markedLogError P j (s+c) Y| ≤ α*(j:ℝ) := hgrowth _ hq₁ hqM₁ _ hjH Y hY
  have he₂ : |markedLogError P (g-j) (p-s) Y| ≤ α*(g-j:ℕ) := hgrowth _ hq₂ (by omega) _ hlargeH Y hY
  have he : |markedLogError P g p Y| ≤ α*(g:ℝ) := hgrowth _ (by omega) (by omega) _ hgH Y hY
  have hl := marked_split_log_ratio_upper P g p j s c hg4 hp hj2 hjhalf hsp hc Y hY B α hB (hA Y hY) he₁ he₂ he
  have hNj : g < j*N := (Nat.div_lt_iff_lt_mul hNpos).mp hj
  have hNjR : (g:ℝ) ≤ (j:ℝ)*N := by exact_mod_cast hNj.le
  have hα4 : α*(4*(N:ℝ))=Real.log 2 := by dsimp [α];field_simp
  have hjDecay : 4*α*(g:ℝ) ≤ (j:ℝ)*Real.log 2 := by
    calc
      _ ≤ 4*α*((j:ℝ)*N) := mul_le_mul_of_nonneg_left hNjR (by positivity)
      _ = _ := by rw [←hα4];ring
  have hl' : Real.log (W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y) ≤ B-α*(g:ℝ) :=
    hl.trans (by nlinarith [show 0 ≤ α*(g:ℝ) by positivity])
  have hW₁ := W_pos P j (s+c) hq₁ (by unfold Stable;omega) Y hY
  have hW₂ := W_pos P (g-j) (p-s) hq₂ (by unfold Stable;omega) Y hY
  have hW := W_pos P g p (by omega) (by unfold Stable;omega) Y hY
  calc
    _ = Real.exp (Real.log (W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y)) :=
      (Real.exp_log (div_pos (mul_pos hW₁ hW₂) hW)).symm
    _ ≤ Real.exp (B-α*(g:ℝ)) := Real.exp_le_exp.mpr hl'
    _ = _ := by rw [←Real.exp_add];congr 1;ring

lemma markedSplitMacroscopic_bound (P : PsiTheory) (p c N : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) (hN : 2 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      markedSplitMacroscopic P g p c N Y ≤ C/(g:ℝ)^2 := by
  obtain ⟨C,α,hC,hα,G,hpoint⟩ := marked_split_macroscopic_decay P p c N hp hc hN
  refine ⟨(2:ℝ)^(p-c)*C*12/α^3,by positivity,max G 1,?_⟩
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
    _ ≤ (2:ℝ)^(p-c)*C*(12/(α^3*(g:ℝ)^2)) :=
      mul_le_mul_of_nonneg_left (Analysis.linear_times_exp_decay_bound α hα g hg1) (by positivity)
    _ = _ := by ring

end WP
