import WPFormalization.Marked.SmallSeparating
import WPFormalization.Marked.MacroscopicSeparating
import WPFormalization.Analysis.SeparatingFiniteAlgebra

/-! Actual finite estimates for the separating terms of Section 6. The
proofs use the original marked W functions and the already proved ratio
and growth bounds; no separating estimate is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace WP

lemma markedSplitConvolution_eq_positive (P : PsiTheory) (g p c : ℕ)
    (hg : 1 ≤ g) (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (Y : ℝ) :
    markedSplitConvolution P g p c Y = 2*markedSplitGenus P g p c 0 Y + markedSplitPositive P g p c Y := by
  have he := Analysis.finite_sum_eq_endpoints_plus_positive g hg (fun j => markedSplitGenus P g p c j Y)
  have hsym := markedSplitGenus_symm P g p c 0 hp hc (by omega) Y
  simp only [Nat.sub_zero] at hsym
  change markedSplitConvolution P g p c Y = markedSplitGenus P g p c 0 Y + markedSplitGenus P g p c g Y + markedSplitPositive P g p c Y at he
  rw [hsym] at he
  linarith

lemma markedSplitPositive_bound (P : PsiTheory) (p c : ℕ) (hp : 2 ≤ p) (hc : c=1 ∨ c=2) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      markedSplitPositive P g p c Y ≤ C/(g:ℝ)^2 := by
  obtain ⟨Cs,hCs,N,hN,hsmall⟩ := markedSplitSmallPositive_bound P p c hp hc
  obtain ⟨Cm,hCm,Gm,hmacro⟩ := markedSplitMacroscopic_bound P p c N hp hc hN
  refine ⟨2*(Cs+Cm),by positivity,max (N*(p+5)) Gm,?_⟩
  intro g hg Y hY
  have hgS : N*(p+5) ≤ g := (le_max_left _ _).trans hg
  have hgM : Gm ≤ g := (le_max_right _ _).trans hg
  have hg2 : 2 ≤ g := by nlinarith
  have hb := Analysis.finite_symmetric_positive_sum_bound g N hg2 hN
    (fun j => markedSplitGenus P g p c j Y)
    (fun j _ => markedSplitGenus_nonneg P g p c j hg2 hp hc Y hY)
    (fun j hj => markedSplitGenus_symm P g p c j hp hc hj Y)
  change markedSplitPositive P g p c Y ≤
    2*(markedSplitSmallPositive P g p c N Y+markedSplitMacroscopic P g p c N Y) at hb
  calc
    _ ≤ 2*(markedSplitSmallPositive P g p c N Y+markedSplitMacroscopic P g p c N Y) := hb
    _ ≤ 2*(Cs/(g:ℝ)^2+Cm/(g:ℝ)^2) := mul_le_mul_of_nonneg_left
      (add_le_add (hsmall g hgS Y hY) (hmacro g hgM Y hY)) (by norm_num)
    _ = _ := by ring

lemma markedSplitConvolution_bound (P : PsiTheory) (p c : ℕ) (hp : 2 ≤ p) (hc : c=1 ∨ c=2) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      markedSplitConvolution P g p c Y ≤ C/(g:ℝ)^(3-c) := by
  obtain ⟨Cp,hCp,Gp,hpos⟩ := markedSplitPositive_bound P p c hp hc
  obtain ⟨Cz,hCz,Gz,hGz,hzero⟩ := markedSplit_genus_zero_bound P p c hp hc
  refine ⟨2*Cz+Cp,by positivity,max Gp Gz,?_⟩
  intro g hg Y hY
  have hgP : Gp ≤ g := (le_max_left _ _).trans hg
  have hgZ : Gz ≤ g := (le_max_right _ _).trans hg
  have hg2 : 2 ≤ g := hGz.trans hgZ
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast (show 1≤g by omega)
  have hgp : 0 < (g:ℝ) := by linarith
  have hp' := hpos g hgP Y hY
  have hz' := hzero g hgZ Y hY
  rw [markedSplitConvolution_eq_positive P g p c (by omega) hp hc Y]
  change markedSplitGenus P g p c 0 Y ≤ Cz/(g:ℝ)^(3-c) at hz'
  rcases hc with rfl|rfl
  · norm_num only [Nat.reduceSub] at hz' ⊢
    calc
      _ ≤ 2*(Cz/(g:ℝ)^2)+Cp/(g:ℝ)^2 := add_le_add
        (mul_le_mul_of_nonneg_left hz' (by norm_num)) hp'
      _ = _ := by ring
  · norm_num only [Nat.reduceSub,pow_one] at hz' ⊢
    have hden : (g:ℝ) ≤ (g:ℝ)^2 := by nlinarith
    have hp'' : markedSplitPositive P g p 2 Y ≤ Cp/(g:ℝ) :=
      hp'.trans (div_le_div_of_nonneg_left hCp.le hgp hden)
    calc
      _ ≤ 2*(Cz/(g:ℝ))+Cp/(g:ℝ) := add_le_add
        (mul_le_mul_of_nonneg_left hz' (by norm_num)) hp''
      _ = _ := by ring

lemma separating_estimates_proof (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Icc (0:ℝ) y₀,
      |separatingS P g p Y| ≤ C/(g:ℝ)^2 ∧ |separatingT P g p Y| ≤ C/(g:ℝ) := by
  obtain ⟨Cs,hCs,Gs,hS⟩ := markedSplitConvolution_bound P p 1 hp (Or.inl rfl)
  obtain ⟨Ct,hCt,Gt,hT⟩ := markedSplitConvolution_bound P p 2 hp (Or.inr rfl)
  refine ⟨Cs+Ct,by positivity,max 2 (max Gs Gt),?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgS : Gs ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgT : Gt ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  rw [separatingS_eq_markedSplitConvolution P g p (by omega) Y,
    separatingT_eq_markedSplitConvolution P g p hp Y,
    abs_of_nonneg (markedSplitConvolution_nonneg P g p 1 hg2 hp (Or.inl rfl) Y hY),
    abs_of_nonneg (markedSplitConvolution_nonneg P g p 2 hg2 hp (Or.inr rfl) Y hY)]
  constructor
  · have h := hS g hgS Y hY
    norm_num only [Nat.reduceSub] at h
    exact h.trans (div_le_div_of_nonneg_right (by linarith : Cs≤Cs+Ct) (by positivity))
  · have h := hT g hgT Y hY
    norm_num only [Nat.reduceSub,pow_one] at h
    exact h.trans (div_le_div_of_nonneg_right (by linarith : Ct≤Cs+Ct) (by positivity))

lemma separatingT_positive_estimate (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |separatingTPositive P g p Y| ≤ C/(g:ℝ)^2 := by
  obtain ⟨C,hC,G,hbound⟩ := markedSplitPositive_bound P p 2 hp (Or.inr rfl)
  refine ⟨C,hC,max G 2,?_⟩
  intro g hg Y hY
  have hgG : G ≤ g := (le_max_left _ _).trans hg
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  rw [separatingTPositive_eq_markedSplitPositive P g p hp Y,
    abs_of_nonneg (markedSplitPositive_nonneg P g p 2 hg2 hp (Or.inr rfl) Y hY)]
  exact hbound g hgG Y hY

lemma separatingT_two_estimate (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |separatingT P g 2 Y| ≤ C/(g:ℝ)^2 := by
  obtain ⟨C,hC,G,hbound⟩ := markedSplitPositive_bound P 2 2 (by norm_num) (Or.inr rfl)
  refine ⟨C,hC,max G 2,?_⟩
  intro g hg Y hY
  have hgG : G ≤ g := (le_max_left _ _).trans hg
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hzero : markedSplitGenus P g 2 2 0 Y = 0 := by
    simp [markedSplitGenus,markedSplitTerm,W_unstable P 0 2 (by norm_num [Stable]) Y]
  rw [separatingT_eq_markedSplitConvolution P g 2 (by norm_num) Y,
    markedSplitConvolution_eq_positive P g 2 2 (by omega) (by norm_num) (Or.inr rfl) Y,
    hzero,mul_zero,zero_add,
    abs_of_nonneg (markedSplitPositive_nonneg P g 2 2 hg2 (by norm_num) (Or.inr rfl) Y hY)]
  exact hbound g hgG Y hY

theorem separating_estimates_exact_type_audit (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |separatingS P g p Y| ≤ C/(g : ℝ)^2 ∧ |separatingT P g p Y| ≤ C/g := by
  exact separating_estimates_proof P p hp

end WP
