import WPFormalization.Marked.SecondProfileProof

/-! Uniqueness of the actual second asymptotic coefficient gives its discrete gradient and arbitrary finite-path independence. PsiTheory remains an explicit model parameter. -/

noncomputable section
open Set

noncomputable section
namespace WP.Analysis
lemma second_coefficient_difference_bound (f₁ f₂ δ₁ δ₂ e₁ e₂ B h C₁ C₂ C₃ : ℝ)
    (hh : 0<h)
    (h₁ : |f₁-(1-δ₁/h+e₁/h^2)| ≤ C₁/h^3)
    (h₂ : |f₂-(1-δ₂/h+e₂/h^2)| ≤ C₂/h^3)
    (h₃ : |(f₁-f₂)-(δ₂-δ₁)/h-B/h^2| ≤ C₃/h^3) :
    |e₁-e₂-B| ≤ (C₁+C₂+C₃)/h := by
  have heq : (e₁-e₂-B)/h^2=
      ((f₁-f₂)-(δ₂-δ₁)/h-B/h^2)-
        (f₁-(1-δ₁/h+e₁/h^2))+(f₂-(1-δ₂/h+e₂/h^2)) := by ring
  have hb : |(e₁-e₂-B)/h^2| ≤ (C₁+C₂+C₃)/h^3 := by
    rw [heq]
    calc
      _ ≤ |(f₁-f₂)-(δ₂-δ₁)/h-B/h^2|+|f₁-(1-δ₁/h+e₁/h^2)|+
          |f₂-(1-δ₂/h+e₂/h^2)| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ C₃/h^3+C₁/h^3+C₂/h^3 := add_le_add (add_le_add h₃ h₁) h₂
      _ = _ := by ring
  rw [abs_div,abs_pow,abs_of_pos hh] at hb
  calc
    _ = (|e₁-e₂-B|/h^2)*h^2 := by field_simp
    _ ≤ ((C₁+C₂+C₃)/h^3)*h^2 := mul_le_mul_of_nonneg_right hb (sq_nonneg h)
    _ = _ := by field_simp <;> ring
end WP.Analysis

noncomputable section
namespace WP.Analysis
lemma complexity_large_inv_coefficient_zero (p : ℕ) (hp : 1 ≤ p) (x C : ℝ)
    (hC : 0 ≤ C) (G : ℕ)
    (hbound : ∀ g ≥ G,2 ≤ g → |x| ≤ C/(complexity g p:ℝ)) : x=0 := by
  by_contra hx
  have hxp : 0 < |x| := abs_pos.mpr hx
  obtain ⟨N,hN⟩ := exists_nat_gt (C/|x|)
  let g := max G (max 2 N)
  have hgG : G ≤ g := le_max_left _ _
  have hg2 : 2 ≤ g := (le_max_left _ _).trans (le_max_right _ _)
  have hgN : N ≤ g := (le_max_right _ _).trans (le_max_right _ _)
  have hgh : g ≤ complexity g p := by unfold complexity;omega
  have hgNR : (N:ℝ) ≤ complexity g p := by exact_mod_cast (hgN.trans hgh)
  have hh : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by omega)
  have hsmall : C/(complexity g p:ℝ)< |x| := by
    apply (div_lt_iff₀ hh).2
    have hi := (div_lt_iff₀ hxp).mp (hN.trans_le hgNR)
    nlinarith
  exact (not_lt_of_ge (hbound g hgG hg2)) hsmall
end WP.Analysis

namespace WP
lemma second_profile_adjacent_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (d : List ℕ) (hd : d.length=p)
    (i : ℕ) (hi : i<d.length) :
    HigherOrder.secondProfile Y (HigherOrder.raiseDegree d i)-HigherOrder.secondProfile Y d=
      -HigherOrder.secondIncrement Y i d := by
  obtain ⟨Ce,hCe,Ge,he⟩ := second_profile_all_degrees_proof P p hp
  obtain ⟨Ca,hCa,Ga,ha⟩ := second_degree_adjacent_small_index P p hp
  let D : ℝ := d.sum
  let K : ℝ := Ce*(D+1)^6+Ce*(D+2)^6+Ca*(D+1)^5
  let G : ℕ := max Ge (max Ga (2*d.sum+2))
  have hD : 0 ≤ D := by dsimp [D];positivity
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hzero : HigherOrder.secondProfile Y d-HigherOrder.secondProfile Y (HigherOrder.raiseDegree d i)-
      HigherOrder.secondIncrement Y i d=0 := by
    apply Analysis.complexity_large_inv_coefficient_zero p hp _ K hK G
    intro g hg hg2
    have hgE : Ge ≤ g := (le_max_left _ _).trans hg
    have hgA : Ga ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
    have hgD : 2*d.sum+2 ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
    have hgh : g ≤ complexity g p := by unfold complexity;omega
    have hsmall : (d.sum:ℝ) ≤ (complexity g p:ℝ)/2 := by
      have hhNat : 2*d.sum ≤ complexity g p := by omega
      have hhR : 2*(d.sum:ℝ) ≤ complexity g p := by exact_mod_cast hhNat
      linarith
    have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by omega)
    have hlen : (HigherOrder.raiseDegree d i).length=p := by rw [HigherOrder.raiseDegree_length,hd]
    have h₁ := he g hgE d hd Y hY
    have h₂ := he g hgE (HigherOrder.raiseDegree d i) hlen Y hY
    rw [HigherOrder.raiseDegree_sum d i hi,Nat.cast_add,Nat.cast_one] at h₂
    have h₂' : |profile P g (HigherOrder.raiseDegree d i) Y-
        (1-degreeCorrection (HigherOrder.raiseDegree d i) Y/(complexity g p:ℝ)+
          HigherOrder.secondProfile Y (HigherOrder.raiseDegree d i)/(complexity g p:ℝ)^2)| ≤
        Ce*(D+2)^6/(complexity g p:ℝ)^3 := by convert h₂ using 1 <;> dsimp [D] <;> ring
    have h₃ := ha g hgA d hd hsmall i hi Y hY
    exact Analysis.second_coefficient_difference_bound _ _ _ _ _ _ _ _
      (Ce*(D+1)^6) (Ce*(D+2)^6) (Ca*(D+1)^5) hhp h₁ h₂' h₃
  linarith
end WP
namespace WP.HigherOrder
lemma secondProfile_zero_tuple (Y : ℝ) (p : ℕ) : secondProfile Y (List.replicate p 0)=0 := by
  simp [secondProfile]

lemma second_profile_path_sum_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (v : ℕ→List ℕ) (i : ℕ→ℕ) (n : ℕ)
    (hlen : ∀ s < n,(v s).length=p) (hi : ∀ s < n,i s<(v s).length)
    (hv : ∀ s < n,v (s+1)=raiseDegree (v s) (i s)) :
    (∑ s∈Finset.range n,secondIncrement Y (i s) (v s))=secondProfile Y (v 0)-secondProfile Y (v n) := by
  calc
    _ = -(∑ s∈Finset.range n,(secondProfile Y (v (s+1))-secondProfile Y (v s))) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      have hs' := Finset.mem_range.mp hs
      have he := WP.second_profile_adjacent_proof P p hp Y hY (v s) (hlen s hs') (i s) (hi s hs')
      rw [←hv s hs'] at he
      linarith
    _ = _ := by rw [Finset.sum_range_sub (fun s => secondProfile Y (v s)) n];ring

lemma second_profile_path_independent_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (v w : ℕ→List ℕ) (i j : ℕ→ℕ) (n m : ℕ)
    (hvlen : ∀ s < n,(v s).length=p) (hwlen : ∀ s < m,(w s).length=p)
    (hi : ∀ s < n,i s<(v s).length) (hj : ∀ s < m,j s<(w s).length)
    (hv : ∀ s < n,v (s+1)=raiseDegree (v s) (i s))
    (hw : ∀ s < m,w (s+1)=raiseDegree (w s) (j s))
    (hstart : v 0=w 0) (hend : v n=w m) :
    (∑ s∈Finset.range n,secondIncrement Y (i s) (v s))=
      ∑ s∈Finset.range m,secondIncrement Y (j s) (w s) := by
  rw [second_profile_path_sum_proof P p hp Y hY v i n hvlen hi hv,
    second_profile_path_sum_proof P p hp Y hY w j m hwlen hj hw,hstart,hend]
end WP.HigherOrder
