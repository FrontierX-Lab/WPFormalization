import WPFormalization.Marked.SecondDegreePrefix

/-! The actual adjacent-degree difference through second order, for every labeled pivot. The finite kernel tail is proved from genuine moments. -/

noncomputable section
open Set

namespace WP
lemma second_degree_adjacent_small (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ t : ℕ,∀ d : List ℕ,(t::d).length=p →
      (((t::d).sum:ℝ) ≤ (complexity g p:ℝ)/2) → ∀ Y∈Icc (0:ℝ) y₀,
      |(profile P g (t::d) Y-profile P g ((t+1)::d) Y)-
        (degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/(complexity g p:ℝ)-
        HigherOrder.secondIncrement Y 0 (t::d)/(complexity g p:ℝ)^2| ≤
        C*(((t::d).sum:ℝ)+1)^5/(complexity g p:ℝ)^3 := by
  obtain ⟨L,hL,Gl,hLayer⟩ := second_degree_layer_uniform P p hp
  obtain ⟨M,hM,hMoment⟩ := Analysis.weight_polynomial_prefix_uniform 5
  obtain ⟨T₁,hT₁,hLeading⟩ := second_leading_adjacent_prefix_uniform p
  obtain ⟨T₂,hT₂,hCorrection⟩ := second_correction_adjacent_prefix_uniform p hp
  refine ⟨L*M+T₁+T₂,by positivity,max 2 Gl,?_⟩
  intro g hg t d hd hsmall Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgL : Gl ≤ g := (le_max_right _ _).trans hg
  have hdlen : d.length+1=p := by simpa only [List.length_cons] using hd
  let h : ℝ := complexity g p
  let N : ℕ := deficit g (t::d)+1
  have hh : 1 ≤ h := by dsimp [h];exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hhp : 0<h := lt_of_lt_of_le zero_lt_one hh
  have hsmallNat : 2*(t::d).sum ≤ complexity g p := by exact_mod_cast (show 2*((t::d).sum:ℝ) ≤ (complexity g p:ℝ) by linarith)
  have had : (t::d).sum ≤ dimension g p := by simp only [complexity,dimension] at hsmallNat ⊢;omega
  have hN : h/2 ≤ (N:ℝ)+1 := by
    have hi : complexity g p ≤ 2*(N+1) := by
      dsimp [N]
      unfold deficit
      rw [hd]
      simp only [complexity,dimension] at hsmallNat ⊢
      omega
    dsimp [h]
    have hi' : (complexity g p:ℝ) ≤ 2*((N:ℝ)+1) := by exact_mod_cast hi
    linarith
  let a (l : ℕ) : ℝ := (4:ℝ)^g*normalizedChildren P g (t+l) (d.map Int.ofNat) Y/W P g p Y
  let b (l : ℕ) : ℝ := (A Y/h)*zeroCountLayer t d l
  let c (l : ℕ) : ℝ := secondDegreeCountLayer Y t d l/h^2
  let B : ℝ := ∑ l∈Finset.range N,weight Y l*b l
  let C₁ : ℝ := ∑ l∈Finset.range N,weight Y l*c l
  have hrec : profile P g (t::d) Y-profile P g ((t+1)::d) Y=
      ∑ l∈Finset.range N,weight Y l*a l := by
    have he := profile_adjacent_degree_difference P g t d (by omega) Y hY
      (by unfold complexity;omega) (by rwa [hdlen])
    rw [hdlen] at he
    exact he
  have herr : |(∑ l∈Finset.range N,weight Y l*a l)-B-C₁| ≤
      (L*M)*(((t::d).sum:ℝ)+1)^5/h^3 := by
    calc
      _ = |∑ l∈Finset.range N,weight Y l*(a l-b l-c l)| := by
        congr 1
        rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ ≤ ∑ l∈Finset.range N,|weight Y l*(a l-b l-c l)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l∈Finset.range N,weight Y l*(L*(((t::d).sum:ℝ)+l+1)^5/h^3) := by
        apply Finset.sum_le_sum
        intro l hl
        rw [abs_mul,abs_of_nonneg (weight_nonneg Y hY l)]
        exact mul_le_mul_of_nonneg_left (hLayer g hgL t d hd l Y hY) (weight_nonneg Y hY l)
      _ = (L/h^3)*(∑ l∈Finset.range N,(((t::d).sum:ℝ)+l+1)^5*weight Y l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ ≤ (L/h^3)*(M*(((t::d).sum:ℝ)+1)^5) :=
        mul_le_mul_of_nonneg_left (hMoment Y hY (t::d).sum N) (by positivity)
      _ = _ := by ring
  have hB : |B-(degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h| ≤
      T₁*(((t::d).sum:ℝ)+1)^5/h^3 := by
    have he := hLeading h hh t d hd N hN Y hY
    have hsum : B=(∑ l∈Finset.range N,(A Y/h)*(weight Y l*zeroCountLayer t d l)) := by
      dsimp [B,b]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [hsum]
    exact he
  have hC₁ : |C₁-HigherOrder.secondIncrement Y 0 (t::d)/h^2| ≤
      T₂*(((t::d).sum:ℝ)+1)^5/h^3 := by
    have he := hCorrection h hh t d hd N hN Y hY
    have hsum : C₁=(∑ l∈Finset.range N,weight Y l*secondDegreeCountLayer Y t d l)/h^2 := by
      dsimp [C₁,c]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [hsum]
    exact he
  rw [hrec]
  have heq : (∑ l∈Finset.range N,weight Y l*a l)-
      (degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h-
      HigherOrder.secondIncrement Y 0 (t::d)/h^2=
      ((∑ l∈Finset.range N,weight Y l*a l)-B-C₁)+
      (B-(degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h)+
      (C₁-HigherOrder.secondIncrement Y 0 (t::d)/h^2) := by ring
  rw [heq]
  calc
    _ ≤ |(∑ l∈Finset.range N,weight Y l*a l)-B-C₁|+
        |B-(degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h|+
        |C₁-HigherOrder.secondIncrement Y 0 (t::d)/h^2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (L*M)*(((t::d).sum:ℝ)+1)^5/h^3+T₁*(((t::d).sum:ℝ)+1)^5/h^3+
        T₂*(((t::d).sum:ℝ)+1)^5/h^3 := add_le_add (add_le_add herr hB) hC₁
    _ = _ := by ring
end WP

namespace WP.HigherOrder
lemma secondIncrement_pivot_eq (Y : ℝ) (d : List ℕ) (i : ℕ) (hi : i<d.length) :
    secondIncrement Y 0 (d[i]!::d.eraseIdx i)=secondIncrement Y i d := by
  have hl : (d.eraseIdx i).length+1=d.length := by rw [List.length_eraseIdx_of_lt hi];omega
  unfold secondIncrement
  simp only [List.length_cons,List.getElem!_cons_zero,List.eraseIdx_zero,List.tail_cons]
  rw [hl]
end WP.HigherOrder
namespace WP
lemma second_degree_adjacent_small_index (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ d : List ℕ,d.length=p →
      (d.sum:ℝ) ≤ (complexity g p:ℝ)/2 → ∀ i : ℕ,i<d.length → ∀ Y∈Icc (0:ℝ) y₀,
      |(profile P g d Y-profile P g (HigherOrder.raiseDegree d i) Y)-
        (degreeCorrection (HigherOrder.raiseDegree d i) Y-degreeCorrection d Y)/(complexity g p:ℝ)-
        HigherOrder.secondIncrement Y i d/(complexity g p:ℝ)^2| ≤
        C*((d.sum:ℝ)+1)^5/(complexity g p:ℝ)^3 := by
  obtain ⟨C,hC,G,hstep⟩ := second_degree_adjacent_small P p hp
  refine ⟨C,hC,G,?_⟩
  intro g hg d hd hsmall i hi Y hY
  have hp₀ : (d[i]!::d.eraseIdx i).Perm d := by
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
      using List.getElem_cons_eraseIdx_perm hi
  have hp₁ : (HigherOrder.raiseDegree d i).Perm ((d[i]!+1)::d.eraseIdx i) :=
    List.set_perm_cons_eraseIdx hi (d[i]!+1)
  have he := hstep g hg (d[i]!) (d.eraseIdx i) (hp₀.length_eq.trans hd)
    (by rwa [hp₀.sum_eq]) Y hY
  rw [profile_perm P g hp₀ Y,←profile_perm P g hp₁ Y,
    HigherOrder.degreeCorrection_perm Y _ _ hp₀,←HigherOrder.degreeCorrection_perm Y _ _ hp₁,
    HigherOrder.secondIncrement_pivot_eq Y d i hi,hp₀.sum_eq] at he
  exact he
end WP
