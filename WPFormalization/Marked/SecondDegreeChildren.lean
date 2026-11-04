import WPFormalization.Marked.FirstDegreeProof
import WPFormalization.Analysis.SecondOrderProfileError

/-! The proved first-degree child expansions rewritten at the parent complexity, without degree restrictions. -/

noncomputable section
open Set

namespace WP
lemma first_degree_child_at_parent_scale (P : PsiTheory) (p q j : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcomp : ∀ g : ℕ,j+2 ≤ g → complexity (g-j) q+1=complexity g p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ d : List ℕ,d.length=q → ∀ Y∈Icc (0:ℝ) y₀,
      |profile P (g-j) d Y-(1-degreeCorrection d Y/(complexity g p:ℝ))| ≤
        C*((d.sum:ℝ)+1)^4/(complexity g p:ℝ)^2 := by
  obtain ⟨C,hC,G,hfirst⟩ := first_degree_all_degrees_proof P q hq
  obtain ⟨B,hB,hdelta⟩ := degreeCorrection_uniform_quadratic_bound q
  refine ⟨4*C+2*B,by positivity,max (G+j) (j+2),?_⟩
  intro g hg d hd Y hY
  have hgG : G ≤ g-j := by have := (le_max_left _ _).trans hg;omega
  have hgJ : j+2 ≤ g := (le_max_right _ _).trans hg
  have hh : (2:ℝ) ≤ complexity g p := by exact_mod_cast (show 2 ≤ complexity g p by unfold complexity;omega)
  have hcNat := hcomp g hgJ
  have hcR : (complexity (g-j) q:ℝ)=(complexity g p:ℝ)-1 := by
    have hc : (complexity (g-j) q:ℝ)+1=(complexity g p:ℝ) := by exact_mod_cast hcNat
    linarith
  have he := hfirst (g-j) hgG d hd Y hY
  rw [hcR] at he
  exact Analysis.child_first_order_parent_scale _ _ _ _ C B hh
    (by linarith [show (0:ℝ) ≤ d.sum from Nat.cast_nonneg _]) hC.le hB.le (hdelta d hd Y hY) he
end WP

namespace WP
lemma second_merger_child_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ t : ℕ,∀ d : List ℕ,(t::d).length=p →
      ∀ l j : ℕ,j<d.length → ∀ Y∈Icc (0:ℝ) y₀,
      |(if 1 ≤ t+d[j]!+l then profile P g (mergerProfile t d l j) Y else 0)-
        (if 1 ≤ t+d[j]!+l then 1-degreeCorrection (mergerProfile t d l j) Y/(complexity g p:ℝ) else 0)| ≤
        C*(((t::d).sum:ℝ)+l+1)^4/(complexity g p:ℝ)^2 := by
  by_cases hp1 : p=1
  · subst p
    refine ⟨1,by norm_num,2,?_⟩
    intro g hg t d hd l j hj Y hY
    simp only [List.length_cons] at hd
    omega
  · have hp2 : 2 ≤ p := by omega
    obtain ⟨C,hC,G,hchild⟩ := first_degree_child_at_parent_scale P p (p-1) 0 hp (by omega) (by
      intro g hg
      simp only [Nat.sub_zero]
      unfold complexity
      omega)
    refine ⟨C,hC,max G 2,?_⟩
    intro g hg t d hd l j hj Y hY
    have hgG : G ≤ g := (le_max_left _ _).trans hg
    have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
    have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
    by_cases hn : 1 ≤ t+d[j]!+l
    · rw [if_pos hn,if_pos hn]
      have hlen : (mergerProfile t d l j).length=p-1 := by
        simp only [mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hj]
        simp only [List.length_cons] at hd
        omega
      have hsum : (mergerProfile t d l j).sum ≤ (t::d).sum+l := by
        have hs : d[j]!+(d.eraseIdx j).sum=d.sum := by simpa [hj] using (List.getElem_cons_eraseIdx_perm hj).sum_eq
        simp only [mergerProfile,List.sum_cons]
        omega
      have hb := hchild g hgG (mergerProfile t d l j) hlen Y hY
      simp only [Nat.sub_zero] at hb
      apply hb.trans
      have hs : ((mergerProfile t d l j).sum:ℝ) ≤ ((t::d).sum:ℝ)+l := by exact_mod_cast hsum
      gcongr
    · rw [if_neg hn,if_neg hn,sub_self,abs_zero]
      positivity

lemma second_handle_child_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ t : ℕ,∀ d : List ℕ,(t::d).length=p →
      ∀ l u : ℕ,u∈Finset.range (t+l-1) → ∀ Y∈Icc (0:ℝ) y₀,
      |profile P (g-1) (contractionProfile t d l u) Y-
        (1-degreeCorrection (contractionProfile t d l u) Y/(complexity g p:ℝ))| ≤
        C*(((t::d).sum:ℝ)+l+1)^4/(complexity g p:ℝ)^2 := by
  obtain ⟨C,hC,G,hchild⟩ := first_degree_child_at_parent_scale P p (p+1) 1 hp (by omega) (by
    intro g hg
    unfold complexity
    omega)
  refine ⟨C,hC,max G 2,?_⟩
  intro g hg t d hd l u hu Y hY
  have hgG : G ≤ g := (le_max_left _ _).trans hg
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hlen : (contractionProfile t d l u).length=p+1 := by
    simp only [contractionProfile,List.length_cons]
    simp only [List.length_cons] at hd
    omega
  have hsum : (contractionProfile t d l u).sum ≤ (t::d).sum+l := by
    have hu' := Finset.mem_range.mp hu
    simp only [contractionProfile,List.sum_cons]
    omega
  have hb := hchild g hgG (contractionProfile t d l u) hlen Y hY
  apply hb.trans
  have hs : ((contractionProfile t d l u).sum:ℝ) ≤ ((t::d).sum:ℝ)+l := by exact_mod_cast hsum
  gcongr
end WP
