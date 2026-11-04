import WPFormalization.Marked.FirstDegreeChildren
import WPFormalization.Analysis.FiniteProfileError
import WPFormalization.Marked.PrefactorRatios
import WPFormalization.Comparison.ZeroPotential

/-! The actual first-order error of one recursion layer. Exact genus factors, quadratic child bounds, genuine second-order prefactors and separating estimates give a uniform cubic error. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP
set_option maxHeartbeats 1000000 in
lemma first_degree_layer_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ t : ℕ, ∀ d : List ℕ, (t::d).length=p →
      ∀ l : ℕ, ∀ Y ∈ Icc (0:ℝ) y₀,
      |(4:ℝ)^g*normalizedChildren P g (t+l) (d.map Int.ofNat) Y/W P g p Y-
        (A Y/(complexity g p:ℝ))*zeroCountLayer t d l| ≤
      C*(((t::d).sum:ℝ)+l+1)^3/(complexity g p:ℝ)^2 := by
  obtain ⟨Em,hEm,Gm,hm⟩ := W_merge_prefactor_second_order P p hp
  obtain ⟨En,hEn,Gn,hn⟩ := W_handle_prefactor_second_order P p hp
  obtain ⟨Qm,hQm,hqm⟩ := merger_child_quadratic_uniform_all P p hp
  obtain ⟨Qn,hQn,hqn⟩ := handle_child_quadratic_uniform P p hp
  obtain ⟨S,hS,Gs,hs⟩ := separatingS_all_complexity_bound P p hp
  obtain ⟨Gp,hPos⟩ := W_eventually_pos_all P (p-1)
  obtain ⟨Ba,hBa,hA⟩ := genusExtension_A_uniform_upper
  let E := Em+En
  let Q := Qm+Qn
  let R := Ba+E
  let K : ℝ := (p:ℝ)+2
  let C := R*Q*(K+2)+E*(K+2)+S
  have hE : 0<E := by dsimp [E];positivity
  have hQ : 0<Q := by dsimp [Q];positivity
  have hR : 0<R := by dsimp [R];positivity
  have hK : 0<K := by dsimp [K];positivity
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,2+Gm+Gn+Gs+Gp,?_⟩
  intro g hg t d hd l Y hY
  have hg2 : 2 ≤ g := by omega
  have hgm : Gm ≤ g := by omega
  have hgn : Gn ≤ g := by omega
  have hgs : Gs ≤ g := by omega
  have hgp : Gp ≤ g := by omega
  have hdlen : d.length+1=p := by simpa only [List.length_cons] using hd
  let h : ℝ := complexity g p
  let B : ℝ := ((t::d).sum:ℝ)+l+1
  have hh : 0<h := by dsimp [h];exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hh1 : 1 ≤ h := by dsimp [h];exact_mod_cast (show 1≤complexity g p by unfold complexity;omega)
  have hB : 1 ≤ B := by dsimp [B];linarith [show (0:ℝ)≤(t::d).sum from Nat.cast_nonneg _,show (0:ℝ)≤l from Nat.cast_nonneg _]
  have hB0 : 0 ≤ B := by linarith
  have hW : 0<W P g p Y := W_pos P g p hp (by unfold Stable;omega) Y hY
  let r₁ := W P g (p-1) Y/W P g p Y
  let r₂ := W P (g-1) (p+1) Y/W P g p Y
  have hr₁ : 0 ≤ r₁ := (div_pos (hPos g hgp Y hY) hW).le
  have hr₂ : 0 ≤ r₂ := div_nonneg (W_nonneg P (g-1) (p+1) (by omega) Y hY) hW.le
  have he₁ : |r₁-A Y/h| ≤ E/h^2 := (hm g hgm Y hY).trans
    (div_le_div_of_nonneg_right (by dsimp [E];linarith : Em≤E) (sq_nonneg h))
  have he₂ : |r₂-A Y/h| ≤ E/h^2 := (hn g hgn Y hY).trans
    (div_le_div_of_nonneg_right (by dsimp [E];linarith : En≤E) (sq_nonneg h))
  have ratio_bound (r : ℝ) (he : |r-A Y/h| ≤ E/h^2) : r ≤ R/h := by
    have hsq : h ≤ h^2 := by nlinarith
    calc r ≤ A Y/h+E/h^2 := by have := (abs_le.mp he).2;linarith
         _ ≤ Ba/h+E/h := add_le_add (div_le_div_of_nonneg_right (hA Y hY) hh.le)
           (div_le_div_of_nonneg_left hE.le hh hsq)
         _ = R/h := by dsimp [R];ring
  let coeff := fun j : ℕ => 2*(d[j]!:ℝ)+1
  let f := fun j : ℕ => if 1 ≤ t+d[j]!+l then profile P g (mergerProfile t d l j) Y else 0
  let bfun := fun j : ℕ => if 1 ≤ t+d[j]!+l then (1:ℝ) else 0
  let a := ∑ j ∈ Finset.range d.length, coeff j*f j
  let b := ∑ j ∈ Finset.range d.length, coeff j*bfun j
  let cm := ∑ j ∈ Finset.range d.length, coeff j
  let c := ∑ u ∈ Finset.range (t+l-1), profile P (g-1) (contractionProfile t d l u) Y
  let n : ℝ := (t+l-1:ℕ)
  let s := (1/2:ℝ)*(4:ℝ)^g*
      (∑ u ∈ Finset.range (t+l-1), ∑ j ∈ Finset.range (g+1),
        ∑ I ∈ (Finset.range d.length).powerset,
          normInt P j ((u:ℤ)::selected (d.map Int.ofNat) I) Y *
          normInt P (g-j) (((t:ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length) \ I)) Y)/W P g p Y
  have hcoeff (j : ℕ) : 0 ≤ coeff j := by dsimp [coeff];positivity
  have hcm : cm ≤ K*B := by
    have hsum : cm=2*(d.sum:ℝ)+d.length := by
      dsimp only [cm,coeff]
      rw [Finset.sum_add_distrib,←Finset.mul_sum]
      have he := sum_range_getElem d (fun k : ℕ => (k:ℝ))
      have hc : (d.map (fun k : ℕ => (k:ℝ))).sum=(d.sum:ℝ) := (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
      rw [hc] at he
      simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    rw [hsum]
    have hdB : (d.sum:ℝ) ≤ B := by dsimp [B];simp only [List.sum_cons,Nat.cast_add];linarith [show (0:ℝ)≤t from Nat.cast_nonneg _,show (0:ℝ)≤l from Nat.cast_nonneg _]
    have hlen : (d.length:ℝ) ≤ p := by exact_mod_cast (show d.length≤p by omega)
    have hpB : (p:ℝ) ≤ (p:ℝ)*B := by nlinarith [mul_nonneg (show (0:ℝ)≤p from Nat.cast_nonneg _) (sub_nonneg.mpr hB)]
    dsimp [K]
    nlinarith
  have hb0 : 0 ≤ b := by
    apply Finset.sum_nonneg;intro j hj
    apply mul_nonneg (hcoeff j)
    dsimp [bfun];split_ifs <;> norm_num
  have hbcm : b ≤ cm := by
    apply Finset.sum_le_sum;intro j hj
    dsimp [bfun]
    split_ifs
    · simp
    · simpa using hcoeff j
  have hn0 : 0 ≤ n := by dsimp [n];positivity
  have hnB : n ≤ B := by
    dsimp [n,B]
    exact_mod_cast (show t+l-1 ≤ (t::d).sum+l+1 by simp only [List.sum_cons];omega)
  have hpoint (j : ℕ) (hj : j∈Finset.range d.length) : |f j-bfun j| ≤ Q*B^2/h := by
    have hi := hqm g hg2 t d hd l j (Finset.mem_range.mp hj) Y hY
    exact hi.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by dsimp [Q];linarith : Qm≤Q) (sq_nonneg B)) hh.le)
  have hmerger : |a-b| ≤ Q*B^2/h*(K*B) := by
    have he := Analysis.finite_weighted_profile_error (Finset.range d.length) coeff f bfun 1 (Q*B^2/h)
      (by norm_num) (fun j hj => hcoeff j) hpoint
    simp only [one_mul] at he
    exact he.trans (mul_le_mul_of_nonneg_left hcm (by positivity))
  have hhandle : |c-n| ≤ Q*B^2/h*B := by
    have he := Analysis.finite_weighted_profile_error (Finset.range (t+l-1)) (fun _ => 1)
      (fun u => profile P (g-1) (contractionProfile t d l u) Y) (fun _ => 1) 1 (Q*B^2/h)
      (by norm_num) (by intros;norm_num) (by
        intro u hu
        rw [abs_sub_comm]
        exact (hqn g hg2 t d hd l u hu Y hY).trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp [Q];linarith : Qn≤Q) (sq_nonneg B)) hh.le))
    simp only [one_mul,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at he
    exact he.trans (mul_le_mul_of_nonneg_left hnB (by positivity))
  have hsep : s ∈ Icc 0 (S*B/h^2) := by
    have hi := normalizedChildren_separating_bound P g t l d hg2 Y hY
    rw [hdlen] at hi
    refine ⟨hi.1,?_⟩
    have hSp : separatingS P g p Y ≤ S/h^2 := (le_abs_self _).trans (hs g hgs Y hY)
    have hbn : ((t+l+1:ℕ):ℝ)/2 ≤ B := by
      have hi : ((t+l+1:ℕ):ℝ) ≤ B := by dsimp [B];exact_mod_cast (show t+l+1 ≤ (t::d).sum+l+1 by simp only [List.sum_cons];omega)
      linarith
    calc s ≤ ((t+l+1:ℕ):ℝ)/2*separatingS P g p Y := hi.2
         _ ≤ ((t+l+1:ℕ):ℝ)/2*(S/h^2) := mul_le_mul_of_nonneg_left hSp (by positivity)
         _ ≤ B*(S/h^2) := mul_le_mul_of_nonneg_right hbn (by positivity)
         _ = _ := by ring
  have hdecomp : (4:ℝ)^g*normalizedChildren P g (t+l) (d.map Int.ofNat) Y/W P g p Y=r₁*a+2*r₂*c+s := by
    have hi := normalizedChildren_scaled_decomposition P g t l d hg2 Y hY
    rw [hdlen] at hi
    simpa only [r₁,r₂,a,c,s,coeff,f,show d.length=p-1 by omega,show d.length+2=p+1 by omega,show p-1+2=p+1 by omega] using hi
  have hcount : zeroCountLayer t d l=b+2*n := rfl
  rw [hdecomp,hcount]
  exact Analysis.layer_first_order_error_bound (A Y) h B K R Q E S r₁ r₂ a b c n s hh hB hK.le hR.le hQ.le hE.le hS.le
    hr₁ hr₂ (ratio_bound r₁ he₁) (ratio_bound r₂ he₂) he₁ he₂ ⟨hb0,hbcm.trans hcm⟩ ⟨hn0,hnB⟩ hmerger hhandle hsep
end WP
