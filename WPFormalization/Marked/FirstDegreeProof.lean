import WPFormalization.Marked.FirstDegreeLayer
import WPFormalization.Marked.FirstDegreeLeading
import WPFormalization.Marked.FirstDegreeLarge

/-! Lemma 7.2 from the actual positive recursion. Finite kernel moments and the leading tail estimate give a cubic adjacent error. Strong induction on degree gives the quartic error at small degrees; the large-degree estimate extends it to all degrees. The original growing-degree statement follows without changing its type. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP
lemma first_degree_adjacent_small (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ t : ℕ, ∀ d : List ℕ, (t::d).length=p →
      (((t::d).sum:ℝ) ≤ (complexity g p:ℝ)/2) → ∀ Y ∈ Icc (0:ℝ) y₀,
      |(profile P g (t::d) Y-profile P g ((t+1)::d) Y)-
        (degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/(complexity g p:ℝ)| ≤
      C*(((t::d).sum:ℝ)+1)^3/(complexity g p:ℝ)^2 := by
  obtain ⟨L,hL,Gl,hLayer⟩ := first_degree_layer_uniform P p hp
  obtain ⟨M,hM,hMoment⟩ := Analysis.weight_polynomial_prefix_uniform 3
  obtain ⟨T,hT,hLeading⟩ := leading_adjacent_prefix_error_uniform p
  refine ⟨L*M+T,by positivity,max 2 Gl,?_⟩
  intro g hg t d hd hsmall Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgl : Gl ≤ g := (le_max_right _ _).trans hg
  have hdlen : d.length+1=p := by simpa only [List.length_cons] using hd
  let h : ℝ := complexity g p
  let N := deficit g (t::d)+1
  have hh1 : 1 ≤ h := by dsimp [h];exact_mod_cast (show 1≤complexity g p by unfold complexity;omega)
  have hhp : 0<h := by linarith
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
  let a := fun l : ℕ => (4:ℝ)^g*normalizedChildren P g (t+l) (d.map Int.ofNat) Y/W P g p Y
  let b := fun l : ℕ => (A Y/h)*zeroCountLayer t d l
  have hrec : profile P g (t::d) Y-profile P g ((t+1)::d) Y=
      ∑ l ∈ Finset.range N, weight Y l*a l := by
    have hi := profile_adjacent_degree_difference P g t d (by omega) Y hY
      (by unfold complexity;omega) (by rwa [hdlen])
    rw [hdlen] at hi
    exact hi
  have herr : |(∑ l ∈ Finset.range N, weight Y l*a l)-
      (∑ l ∈ Finset.range N, (A Y/h)*(weight Y l*zeroCountLayer t d l))| ≤
      (L*M)*(((t::d).sum:ℝ)+1)^3/h^2 := by
    calc _ = |∑ l ∈ Finset.range N, weight Y l*(a l-b l)| := by
           congr 1
           rw [←Finset.sum_sub_distrib]
           apply Finset.sum_congr rfl
           intro l hl
           dsimp [b]
           ring
         _ ≤ ∑ l ∈ Finset.range N, |weight Y l*(a l-b l)| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ l ∈ Finset.range N, weight Y l*(L*(((t::d).sum:ℝ)+l+1)^3/h^2) := by
           apply Finset.sum_le_sum
           intro l hl
           rw [abs_mul,abs_of_nonneg (weight_nonneg Y hY l)]
           exact mul_le_mul_of_nonneg_left (hLayer g hgl t d hd l Y hY) (weight_nonneg Y hY l)
         _ = (L/h^2)*(∑ l ∈ Finset.range N, (((t::d).sum:ℝ)+l+1)^3*weight Y l) := by
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro l hl
           ring
         _ ≤ (L/h^2)*(M*(((t::d).sum:ℝ)+1)^3) := mul_le_mul_of_nonneg_left
           (hMoment Y hY (t::d).sum N) (by positivity)
         _ = _ := by ring
  have ht := hLeading h hh1 t d hd N hN Y hY
  rw [hrec]
  calc _ ≤ |(∑ l ∈ Finset.range N, weight Y l*a l)-
          (∑ l ∈ Finset.range N, (A Y/h)*(weight Y l*zeroCountLayer t d l))|+
          |(∑ l ∈ Finset.range N, (A Y/h)*(weight Y l*zeroCountLayer t d l))-
            (degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h| :=
           abs_sub_le _ _ _
       _ ≤ (L*M)*(((t::d).sum:ℝ)+1)^3/h^2+T*(((t::d).sum:ℝ)+1)^3/h^2 := add_le_add herr ht
       _ = _ := by ring
end WP
namespace WP
lemma first_degree_small_telescope (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) (g : ℕ) (hg : 1 ≤ g)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ t : ℕ, ∀ e : List ℕ, (t::e).length=p →
      (((t::e).sum:ℝ) ≤ (complexity g p:ℝ)/2) →
      |(profile P g (t::e) Y-profile P g ((t+1)::e) Y)-
        (degreeCorrection ((t+1)::e) Y-degreeCorrection (t::e) Y)/(complexity g p:ℝ)| ≤
      C*(((t::e).sum:ℝ)+1)^3/(complexity g p:ℝ)^2) :
    ∀ d : List ℕ, d.length=p → (d.sum:ℝ) ≤ (complexity g p:ℝ)/2 →
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g p:ℝ))| ≤
      C*((d.sum:ℝ)+1)^4/(complexity g p:ℝ)^2 := by
  have hst : Stable g p := by unfold Stable;omega
  have hbound : ∀ n : ℕ, ∀ d : List ℕ, d.sum=n → d.length=p →
      (d.sum:ℝ) ≤ (complexity g p:ℝ)/2 →
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g p:ℝ))| ≤
      C*(d.sum:ℝ)*((d.sum:ℝ)+1)^3/(complexity g p:ℝ)^2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hd hlen hsmall
      by_cases hz : d.sum=0
      · have he : d=List.replicate d.length 0 := List.eq_replicate_of_mem (List.sum_eq_zero_iff_forall_eq_nat.mp hz)
        rw [he,hlen,profile_replicate_zero P g p hp hst Y hY,HigherOrder.degreeCorrection_zero_tuple]
        simp
      · obtain ⟨a,ha,hapos⟩ := List.sum_pos_iff_exists_pos_nat.mp (Nat.pos_of_ne_zero hz)
        obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hapos)
        obtain ⟨l,r,rfl⟩ := List.mem_iff_append.mp ha
        let e := l++k::r
        have helen : e.length=p := by simpa only [e,List.length_append,List.length_cons] using hlen
        have hes : e.sum<n := by simp only [e,List.sum_append,List.sum_cons] at hd ⊢;omega
        have hsum : (l++(k+1)::r).sum=e.sum+1 := by simp only [e,List.sum_append,List.sum_cons];omega
        have hesmall : (e.sum:ℝ) ≤ (complexity g p:ℝ)/2 := by
          rw [hsum,Nat.cast_add,Nat.cast_one] at hsmall
          linarith
        have hprev := ih e.sum hes e rfl helen hesmall
        have hp₀ : e.Perm (k::(l++r)) := List.perm_middle
        have hp₁ : (l++(k+1)::r).Perm ((k+1)::(l++r)) := List.perm_middle
        have hlen' : (k::(l++r)).length=p := hp₀.length_eq.symm.trans helen
        have hsmall' : ((k::(l++r)).sum:ℝ) ≤ (complexity g p:ℝ)/2 := by rw [←hp₀.sum_eq];exact hesmall
        have hinc := hstep k (l++r) hlen' hsmall'
        rw [←profile_perm P g hp₀ Y,←profile_perm P g hp₁ Y,
          ←HigherOrder.degreeCorrection_perm Y _ _ hp₀,←HigherOrder.degreeCorrection_perm Y _ _ hp₁,
          ←hp₀.sum_eq] at hinc
        have heq : profile P g (l++(k+1)::r) Y-(1-degreeCorrection (l++(k+1)::r) Y/(complexity g p:ℝ)) =
          (profile P g e Y-(1-degreeCorrection e Y/(complexity g p:ℝ)))-
          ((profile P g e Y-profile P g (l++(k+1)::r) Y)-
            (degreeCorrection (l++(k+1)::r) Y-degreeCorrection e Y)/(complexity g p:ℝ)) := by ring
        rw [heq,hsum,Nat.cast_add,Nat.cast_one]
        calc _ ≤ |profile P g e Y-(1-degreeCorrection e Y/(complexity g p:ℝ))|+
            |(profile P g e Y-profile P g (l++(k+1)::r) Y)-
              (degreeCorrection (l++(k+1)::r) Y-degreeCorrection e Y)/(complexity g p:ℝ)| := abs_sub _ _
             _ ≤ C*(e.sum:ℝ)*((e.sum:ℝ)+1)^3/(complexity g p:ℝ)^2+
                 C*((e.sum:ℝ)+1)^3/(complexity g p:ℝ)^2 := add_le_add hprev hinc
             _ = C*((e.sum:ℝ)+1)*((e.sum:ℝ)+1)^3/(complexity g p:ℝ)^2 := by ring
             _ ≤ _ := by
               apply div_le_div_of_nonneg_right _ (sq_nonneg _)
               have hi := pow_le_pow_left₀ (show (0:ℝ)≤(e.sum:ℝ)+1 by positivity)
                 (show (e.sum:ℝ)+1 ≤ (e.sum:ℝ)+1+1 by linarith) 3
               exact mul_le_mul_of_nonneg_left hi (by positivity)
  intro d hd hsmall
  calc _ ≤ C*(d.sum:ℝ)*((d.sum:ℝ)+1)^3/(complexity g p:ℝ)^2 := hbound d.sum d rfl hd hsmall
       _ ≤ _ := by
         apply div_le_div_of_nonneg_right _ (sq_nonneg _)
         have hi := mul_le_mul_of_nonneg_left (show (d.sum:ℝ) ≤ (d.sum:ℝ)+1 by linarith)
           (show 0 ≤ C*((d.sum:ℝ)+1)^3 by positivity)
         nlinarith

lemma first_degree_all_degrees_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ d : List ℕ, d.length=p → ∀ Y ∈ Icc (0:ℝ) y₀,
      |profile P g d Y-(1-degreeCorrection d Y/(complexity g p:ℝ))| ≤
      C*((d.sum:ℝ)+1)^4/(complexity g p:ℝ)^2 := by
  obtain ⟨Cs,hCs,G,hstep⟩ := first_degree_adjacent_small P p hp
  obtain ⟨Cb,hCb,hbig⟩ := large_degree_profile_first_order P p hp
  refine ⟨Cs+Cb,by positivity,max 2 G,?_⟩
  intro g hg d hd Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgg : G ≤ g := (le_max_right _ _).trans hg
  by_cases hsmall : (d.sum:ℝ) ≤ (complexity g p:ℝ)/2
  · have hi := first_degree_small_telescope P p hp g (by omega) Y hY Cs hCs.le
      (fun t e he hs => hstep g hgg t e he hs Y hY) d hd hsmall
    exact hi.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : Cs≤Cs+Cb)
      (by positivity)) (sq_nonneg _))
  · have hi := hbig g (by omega) d hd Y hY (by linarith)
    exact hi.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : Cb≤Cs+Cb)
      (by positivity)) (sq_nonneg _))

lemma first_degree_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ d : List ℕ, d.length = p →
    (d.sum : ℝ) ≤ Real.rpow (complexity g p) (1/4 : ℝ) →
    ∀ Y ∈ Set.Icc 0 y₀,
      |profile P g d Y - (1-degreeCorrection d Y/complexity g p)| ≤
        C*(d.sum+1 : ℝ)^4/(complexity g p : ℝ)^2 := by
  obtain ⟨C,hC,G,hbound⟩ := first_degree_all_degrees_proof P p hp
  exact ⟨C,hC,G,fun g hg d hd _ Y hY => hbound g hg d hd Y hY⟩
end WP
