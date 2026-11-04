import WPFormalization.Analysis.TopologyLossBounds
import WPFormalization.Marked.UniformComplexityGrowth
import WPFormalization.Marked.IteratedRatios
import WPFormalization.Marked.FiniteFamilies
import WPFormalization.Marked.SeparatingDefinitions
import WPFormalization.Marked.GrowingMacroscopic

/-! Actual small-complexity contributions, grouped at each loss r. A single constant controls all marking and loss orders; Vandermonde removes the subset factorial cost. -/
noncomputable section
namespace WP
open Set
lemma markedSplitTerm_uniform_loss_power (P : PsiTheory) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ g p c j s : ℕ, 2 ≤ g → 2 ≤ p →
      c=1 ∨ c=2 → 2*j ≤ g → s<p → ∀Y∈Icc (0:ℝ) y₀,
      markedSplitTerm P g p c j s Y ≤ (Nat.choose (p-c) s:ℝ)*
        ((2*j+s-1).factorial:ℝ)*(D/(g:ℝ))^(2*j+s) := by
  obtain ⟨T,hT,hbound⟩ := W_uniform_complexity_exponential P
  obtain ⟨Cr,hCr,hratio⟩ := W_small_genus_ratio_uniform
  let D : ℝ := max 1 (T*Cr)
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨D,hD,?_⟩
  intro g p c j s hg hp hc hj hs Y hY
  have hq : 1 ≤ s+c := by rcases hc with rfl|rfl <;>omega
  have hgR : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  by_cases hst : Stable j (s+c)
  · let r : ℕ := 2*j+s
    let a : ℕ := complexity j (s+c)
    have ha : 1 ≤ a := by dsimp [a];unfold complexity;unfold Stable at hst;omega
    have har : a ≤ r := by rcases hc with rfl|rfl <;>dsimp [a,r] <;>unfold complexity <;>omega
    have hgma : Real.Gamma (a:ℝ) = ((a-1).factorial:ℝ) := by
      have he : ((a-1:ℕ):ℝ)+1=(a:ℝ) := by exact_mod_cast (show a-1+1=a by omega)
      simpa only [he] using Real.Gamma_nat_eq_factorial (a-1)
    have hfact : Real.Gamma (a:ℝ) ≤ ((r-1).factorial:ℝ) := by
      rw [hgma]
      exact_mod_cast Nat.factorial_le (show a-1 ≤ r-1 by omega)
    have hw : W P j (s+c) Y ≤ ((r-1).factorial:ℝ)*T^r := by
      exact (hbound j (s+c) hst Y hY).trans
        (mul_le_mul hfact (pow_le_pow_right₀ hT har) (by positivity) (by positivity))
    have hrat := hratio P g p j s hg hp hj hs Y hY
    have hscale : T*(Cr/(g:ℝ)) ≤ D/(g:ℝ) := by
      have he := div_le_div_of_nonneg_right (le_max_right 1 (T*Cr)) hgR.le
      convert he using 1 <;>ring
    calc
      _ = (Nat.choose (p-c) s:ℝ)*W P j (s+c) Y*(W P (g-j) (p-s) Y/W P g p Y) := by unfold markedSplitTerm;ring
      _ ≤ (Nat.choose (p-c) s:ℝ)*(((r-1).factorial:ℝ)*T^r)*(Cr/(g:ℝ))^r := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
        · exact hrat
        · exact div_nonneg (W_nonneg P (g-j) (p-s) (by omega) Y hY)
            (W_pos P g p (by omega) (by unfold Stable;omega) Y hY).le
        · positivity
      _ = (Nat.choose (p-c) s:ℝ)*((r-1).factorial:ℝ)*(T*(Cr/(g:ℝ)))^r := by rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hscale r) (by positivity)
  · rw [markedSplitTerm,W_unstable P j (s+c) hst Y]
    simp only [mul_zero,zero_mul,zero_div]
    positivity
noncomputable def markedSplitLossLayer (P : PsiTheory) (g p c N r : ℕ) (Y : ℝ) : ℝ :=
  ∑ a ∈ ((Finset.range (g/N+1)).product (Finset.range (p-c+1))).filter
    (fun a=>2*a.1+a.2=r), markedSplitTerm P g p c a.1 a.2 Y
lemma markedSplitLossLayer_uniform (P : PsiTheory) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ g p c N r : ℕ, 2 ≤ g → 2 ≤ p →
      (c=1 ∨ c=2) → 2 ≤ N → 1 ≤ r → ∀Y∈Icc (0:ℝ) y₀,
      markedSplitLossLayer P g p c N r Y ≤ (D*((p:ℝ)+r)/(g:ℝ))^r := by
  obtain ⟨D,hD,hbound⟩ := markedSplitTerm_uniform_loss_power P
  refine ⟨D,hD,?_⟩
  intro g p c N r hg hp hc hN hr Y hY
  let S := ((Finset.range (g/N+1)).product (Finset.range (p-c+1))).filter (fun a=>2*a.1+a.2=r)
  have hD0 : 0 ≤ D := by linarith
  have hpre : markedSplitLossLayer P g p c N r Y ≤
      ∑ s ∈ Finset.range (r+1), (Nat.choose (p-c) s:ℝ)*((r-1).factorial:ℝ)*(D/(g:ℝ))^r := by
    unfold markedSplitLossLayer
    apply Finset.sum_le_sum_of_injOn (fun a : ℕ×ℕ=>a.2)
    · intro a ha b hb hab
      have hra := (Finset.mem_filter.mp ha).2
      have hrb := (Finset.mem_filter.mp hb).2
      apply Prod.ext <;>dsimp at * <;>omega
    · intro s hs
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
      have hra := (Finset.mem_filter.mp ha).2
      exact Finset.mem_range.mpr (by omega)
    · intro a ha
      obtain ⟨hab,hra⟩ := Finset.mem_filter.mp ha
      obtain ⟨hj,hs⟩ := Finset.mem_product.mp hab
      have hjN : a.1 ≤ g/N := by have he := Finset.mem_range.mp hj;omega
      have hNj : a.1*N ≤ g := (Nat.le_div_iff_mul_le (by omega : 0<N)).mp hjN
      have hj2 : 2*a.1 ≤ g := by nlinarith only [hNj,hN]
      have hsp : a.2 < p := by
        have he := Finset.mem_range.mp hs
        rcases hc with rfl|rfl <;>omega
      have ht := hbound g p c a.1 a.2 hg hp hc hj2 hsp Y hY
      rwa [hra] at ht
    · intro s hs hnot
      positivity
  calc
    _ ≤ ∑ s ∈ Finset.range (r+1), (Nat.choose (p-c) s:ℝ)*((r-1).factorial:ℝ)*(D/(g:ℝ))^r := hpre
    _ = (D/(g:ℝ))^r*(((r-1).factorial:ℝ)*∑ s ∈ Finset.range (r+1), (Nat.choose (p-c) s:ℝ)) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ (D/(g:ℝ))^r*((r.factorial:ℝ)*∑ s ∈ Finset.range (r+1), (Nat.choose (p-c) s:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.factorial_le (Nat.sub_le r 1)
    _ ≤ (D/(g:ℝ))^r*((p-c+r:ℕ):ℝ)^r := mul_le_mul_of_nonneg_left
      (Analysis.subset_loss_factorial_sum (p-c) r) (by positivity)
    _ ≤ (D/(g:ℝ))^r*((p:ℝ)+r)^r := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (show p-c+r ≤ p+r by omega)
    _ = _ := by rw [←mul_pow];congr 1;ring
noncomputable def markedSplitSmallLossTail (P : PsiTheory) (g p c N L : ℕ) (Y : ℝ) : ℝ :=
  ∑ a ∈ (Finset.range (g/N+1)).product (Finset.range (p-c+1)),
    if L ≤ 2*a.1+a.2 then markedSplitTerm P g p c a.1 a.2 Y else 0
lemma markedSplitSmallLossTail_layers (P : PsiTheory) (g p c N L : ℕ) (Y : ℝ) :
    markedSplitSmallLossTail P g p c N L Y =
      ∑ r ∈ Finset.range (2*(g/N)+(p-c)+1), if L ≤ r then markedSplitLossLayer P g p c N r Y else 0 := by
  let S := (Finset.range (g/N+1)).product (Finset.range (p-c+1))
  have hmap : ∀ a ∈ S, 2*a.1+a.2 ∈ Finset.range (2*(g/N)+(p-c)+1) := by
    intro a ha
    obtain ⟨hj,hs⟩ := Finset.mem_product.mp ha
    have hj0 := Finset.mem_range.mp hj
    have hs0 := Finset.mem_range.mp hs
    exact Finset.mem_range.mpr (by omega)
  have hspl := Finset.sum_fiberwise_of_maps_to hmap
    (fun a=>if L ≤ 2*a.1+a.2 then markedSplitTerm P g p c a.1 a.2 Y else 0)
  change (∑a∈S,if L ≤ 2*a.1+a.2 then markedSplitTerm P g p c a.1 a.2 Y else 0)=_
  rw [←hspl]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hLr : L ≤ r
  · rw [if_pos hLr]
    apply Finset.sum_congr rfl
    intro a ha
    have he := (Finset.mem_filter.mp ha).2
    rw [he,if_pos hLr]
  · rw [if_neg hLr]
    apply Finset.sum_eq_zero
    intro a ha
    have he := (Finset.mem_filter.mp ha).2
    rw [he,if_neg hLr]
lemma markedSplitSmallLossTail_cut_bound (P : PsiTheory) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ g p c N L : ℕ, 2 ≤ g → 2 ≤ p →
      (c=1 ∨ c=2) → 2 ≤ N → 1 ≤ L →
      2*Real.exp 1*D*((p:ℝ)+(2*(g/N)+(p-c):ℕ)+2) ≤ g → ∀Y∈Icc (0:ℝ) y₀,
      markedSplitSmallLossTail P g p c N L Y ≤ 2*(D*((p:ℝ)+L)/(g:ℝ))^L := by
  obtain ⟨D,hD,hbound⟩ := markedSplitLossLayer_uniform P
  refine ⟨D,hD,?_⟩
  intro g p c N L hg hp hc hN hL hcut Y hY
  rw [markedSplitSmallLossTail_layers]
  have he : (∑r∈Finset.range (2*(g/N)+(p-c)+1),if L ≤ r then markedSplitLossLayer P g p c N r Y else 0) ≤
      ∑r∈Finset.range (2*(g/N)+(p-c)+1),if L ≤ r then (D*((p:ℝ)+r)/(g:ℝ))^r else 0 := by
    apply Finset.sum_le_sum
    intro r hr
    by_cases hLr : L ≤ r
    · rw [if_pos hLr,if_pos hLr]
      exact hbound g p c N r hg hp hc hN (by omega) Y hY
    · rw [if_neg hLr,if_neg hLr]
  exact he.trans (Analysis.finite_loss_power_tail_filter (p:ℝ) D g L (2*(g/N)+(p-c))
    (Nat.cast_nonneg _) (by linarith) (by exact_mod_cast (show 0<g by omega)) hL hcut)
lemma small_loss_sqrt_marking_cutoff (D M : ℝ) (hD : 1 ≤ D) (hM : 0 < M) :
    ∃ N G : ℕ, 2 ≤ N ∧ ∀ g ≥ G, ∀ p : ℕ, 2 ≤ p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀ c : ℕ,
      2*Real.exp 1*D*((p:ℝ)+(2*(g/N)+(p-c):ℕ)+2) ≤ g := by
  let K : ℝ := Real.exp 1*D
  have hK : 0 < K := by dsimp [K];positivity
  let x : ℝ := 64*K*M
  have hx : 0 ≤ x := by dsimp [x];positivity
  obtain ⟨N,hN⟩ := exists_nat_ge (16*K+2)
  have hN2 : 2 ≤ N := by exact_mod_cast (show (2:ℝ) ≤ N by linarith)
  obtain ⟨G,hG⟩ := exists_nat_ge (max (4*M^2+1) (x^2+16*K+4))
  refine ⟨N,G,hN2,?_⟩
  intro g hg p hp hpM c
  have hgR : (G:ℝ) ≤ g := by exact_mod_cast hg
  have hgM : 4*M^2+1 ≤ (g:ℝ) := (le_max_left _ _).trans (hG.trans hgR)
  have hgl : x^2+16*K+4 ≤ (g:ℝ) := (le_max_right _ _).trans (hG.trans hgR)
  have hg2 : 2 ≤ g := by
    exact_mod_cast (show (2:ℝ) ≤ g by nlinarith only [hgl,hK,sq_nonneg x])
  have hg0 : (0:ℝ) ≤ g := Nat.cast_nonneg _
  have hroot : x ≤ Real.sqrt (g:ℝ) := by
    nlinarith only [Real.sq_sqrt hg0,Real.sqrt_nonneg (g:ℝ),hgl,hK,hx]
  have hcomp : (complexity g p:ℝ) ≤ 4*(g:ℝ) :=
    complexity_le_four_genus_growing g p (by unfold Stable;omega) M hM hpM
      (hgM.trans (by exact_mod_cast (show g ≤ complexity g p by unfold complexity;omega)))
  have hsqrt := Analysis.sqrt_scale_bound _ _ 4 (by norm_num) hcomp
  have hpc : (p:ℝ) ≤ 4*M*Real.sqrt (g:ℝ) := by
    have he := mul_le_mul_of_nonneg_left hsqrt hM.le
    nlinarith only [hpM,he]
  have hpcut : 16*K*(p:ℝ) ≤ g := by
    have he1 := mul_le_mul_of_nonneg_left hpc (show 0 ≤ 16*K by positivity)
    have he2 := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (g:ℝ))
    dsimp [x] at he2
    nlinarith only [he1,he2,Real.sq_sqrt hg0]
  have hfloor : ((g/N:ℕ):ℝ)*(N:ℝ) ≤ g := by exact_mod_cast Nat.div_mul_le_self g N
  have hfloorcut : 16*K*((g/N:ℕ):ℝ) ≤ g := by
    have he := mul_le_mul_of_nonneg_right hN (show (0:ℝ) ≤ (g/N:ℕ) by positivity)
    nlinarith only [he,hfloor,show (0:ℝ) ≤ (g/N:ℕ) from Nat.cast_nonneg _]
  have hc : ((p-c:ℕ):ℝ) ≤ p := by exact_mod_cast Nat.sub_le p c
  have hgc : 16*K ≤ (g:ℝ) := by nlinarith only [hgl,sq_nonneg x]
  have hpc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*K by positivity)
  rw [show 2*Real.exp 1*D=2*K by dsimp [K];ring]
  push_cast
  nlinarith only [hpcut,hfloorcut,hgc,hpc',hg0]
end WP
