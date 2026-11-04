import WPFormalization.Marked.SecondDegreeProducts
import WPFormalization.Marked.SecondSeparatingLayer

/-! The complete original recursion layer through second order. Every child and both minimal separating types are actual normalized amplitudes. -/

noncomputable section
open Set

namespace WP

def secondDegreeCountLayer (Y : ℝ) (t : ℕ) (d : List ℕ) (l : ℕ) : ℝ :=
  A Y*(∑ j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
    (if 1 ≤ t+d[j]!+l then 1-transportBeta d.length Y-degreeCorrection (mergerProfile t d l j) Y else 0))+
  2*A Y*(∑ u∈Finset.range (t+l-1),
    (1-transportBeta (d.length+2) Y-HigherOrder.alpha (d.length+1) Y-degreeCorrection (contractionProfile t d l u) Y))+
  (A Y)^2*((if 2 ≤ t+l then (Nat.choose (zeros d) 2:ℝ)+theta Y 1/2 else 0)+
    (if 3 ≤ t+l then (1/2:ℝ) else 0))

lemma second_degree_layer_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ t : ℕ,∀ d : List ℕ,(t::d).length=p →
      ∀ l : ℕ,∀ Y∈Icc (0:ℝ) y₀,
      |(4:ℝ)^g*normalizedChildren P g (t+l) (d.map Int.ofNat) Y/W P g p Y-
        (A Y/(complexity g p:ℝ))*zeroCountLayer t d l-
        secondDegreeCountLayer Y t d l/(complexity g p:ℝ)^2| ≤
        C*(((t::d).sum:ℝ)+l+1)^5/(complexity g p:ℝ)^3 := by
  obtain ⟨Cm,hCm,Gm,hm⟩ := second_merger_product_uniform P p hp
  obtain ⟨Ch,hCh,Gh,hh⟩ := second_handle_product_uniform P p hp
  obtain ⟨Cs,hCs,Gs,hs⟩ := secondSeparatingLayer_uniform P p hp
  let K : ℝ := (p:ℝ)+2
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨Cm*K+Ch+Cs,by positivity,max 3 (max Gm (max Gh Gs)),?_⟩
  intro g hg t d hd l Y hY
  have hg3 : 3 ≤ g := (le_max_left _ _).trans hg
  have hgM : Gm ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgH : Gh ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hg))
  have hgS : Gs ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hg))
  have hdlen : d.length+1=p := by simpa only [List.length_cons] using hd
  let h : ℝ := complexity g p
  let L : ℝ := ((t::d).sum:ℝ)+l+1
  have hhp : 0<h := by dsimp [h];exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hL : 1 ≤ L := by dsimp [L];linarith [show (0:ℝ) ≤ (t::d).sum from Nat.cast_nonneg _,show (0:ℝ) ≤ l from Nat.cast_nonneg _]
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  let coeff (j : ℕ) : ℝ := 2*(d[j]!:ℝ)+1
  let fm (j : ℕ) : ℝ := if 1 ≤ t+d[j]!+l then profile P g (mergerProfile t d l j) Y else 0
  let um (j : ℕ) : ℝ := if 1 ≤ t+d[j]!+l then 1 else 0
  let vm (j : ℕ) : ℝ := if 1 ≤ t+d[j]!+l then 1-transportBeta (p-1) Y-degreeCorrection (mergerProfile t d l j) Y else 0
  let fh (u : ℕ) : ℝ := profile P (g-1) (contractionProfile t d l u) Y
  let vh (u : ℕ) : ℝ := 1-transportBeta (p+1) Y-HigherOrder.alpha p Y-degreeCorrection (contractionProfile t d l u) Y
  let r₁ : ℝ := W P g (p-1) Y/W P g p Y
  let r₂ : ℝ := W P (g-1) (p+1) Y/W P g p Y
  let a : ℝ := r₁*(∑ j∈Finset.range d.length,coeff j*fm j)
  let b : ℝ := ∑ j∈Finset.range d.length,coeff j*um j
  let bm : ℝ := ∑ j∈Finset.range d.length,coeff j*vm j
  let c : ℝ := 2*r₂*(∑ u∈Finset.range (t+l-1),fh u)
  let n : ℝ := (t+l-1:ℕ)
  let bh : ℝ := ∑ u∈Finset.range (t+l-1),vh u
  let s : ℝ := secondSeparatingLayer P g (t+l) d Y
  let v : ℝ := (if 2 ≤ t+l then (Nat.choose (zeros d) 2:ℝ)+theta Y 1/2 else 0)+
    (if 3 ≤ t+l then (1/2:ℝ) else 0)
  have hcoeff (j : ℕ) : 0 ≤ coeff j := by dsimp [coeff];positivity
  have hcm : (∑ j∈Finset.range d.length,coeff j) ≤ K*L := by
    have hsum : (∑ j∈Finset.range d.length,coeff j)=2*(d.sum:ℝ)+d.length := by
      dsimp only [coeff]
      rw [Finset.sum_add_distrib,←Finset.mul_sum]
      have he := sum_range_getElem d (fun k : ℕ => (k:ℝ))
      have hc : (d.map (fun k : ℕ => (k:ℝ))).sum=(d.sum:ℝ) := (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
      rw [hc] at he
      simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    rw [hsum]
    have hdL : (d.sum:ℝ) ≤ L := by dsimp [L];simp only [List.sum_cons,Nat.cast_add];linarith [show (0:ℝ) ≤ t from Nat.cast_nonneg _,show (0:ℝ) ≤ l from Nat.cast_nonneg _]
    have hlen : (d.length:ℝ) ≤ p := by exact_mod_cast (show d.length ≤ p by omega)
    have hpL : (p:ℝ) ≤ (p:ℝ)*L := by nlinarith [mul_nonneg (show (0:ℝ) ≤ p from Nat.cast_nonneg _) (sub_nonneg.mpr hL)]
    dsimp [K]
    nlinarith
  have hnL : n ≤ L := by
    dsimp [n,L]
    exact_mod_cast (show t+l-1 ≤ (t::d).sum+l+1 by simp only [List.sum_cons];omega)
  have hmerger : |a-(A Y/h)*b-(A Y/h^2)*bm| ≤ Cm*K*L^5/h^3 := by
    have he := Analysis.finite_weighted_two_scales_error (Finset.range d.length) coeff
      (fun j => r₁*fm j) um vm (A Y/h) (A Y/h^2) (Cm*L^4/h^3)
      (fun j _ => hcoeff j) (fun j hj => hm g hgM t d hd l j (Finset.mem_range.mp hj) Y hY)
    have heq : (∑ j∈Finset.range d.length,coeff j*(r₁*fm j))=a := by
      dsimp [a]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq] at he
    calc
      _ ≤ Cm*L^4/h^3*(∑ j∈Finset.range d.length,coeff j) := he
      _ ≤ Cm*L^4/h^3*(K*L) := mul_le_mul_of_nonneg_left hcm (by positivity)
      _ = _ := by ring
  have hhandle : |c-(2*A Y/h)*n-(2*A Y/h^2)*bh| ≤ Ch*L^5/h^3 := by
    have he := Analysis.finite_weighted_two_scales_error (Finset.range (t+l-1)) (fun _ => 1)
      (fun u => 2*r₂*fh u) (fun _ => 1) vh (2*A Y/h) (2*A Y/h^2) (Ch*L^4/h^3)
      (by intros;norm_num) (by intro u hu;simpa only [mul_one] using hh g hgH t d hd l u hu Y hY)
    simp only [one_mul,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at he
    rw [←Finset.mul_sum] at he
    calc
      _ ≤ Ch*L^4/h^3*n := he
      _ ≤ Ch*L^4/h^3*L := mul_le_mul_of_nonneg_left hnL (by positivity)
      _ = _ := by ring
  have hsep : |s-(A Y)^2/h^2*v| ≤ Cs*L^5/h^3 := by
    have he := hs g hgS (t+l) d hdlen Y hY
    have hsum : ((t+l+d.sum:ℕ)+1:ℝ)=L := by
      dsimp [L]
      simp only [List.sum_cons,Nat.cast_add]
      ring
    rw [hsum] at he
    exact he.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by norm_num) : L^2 ≤ L^5) hCs.le) (by positivity))
  have hdecomp : (4:ℝ)^g*normalizedChildren P g (t+l) (d.map Int.ofNat) Y/W P g p Y=a+c+s := by
    have he := normalizedChildren_scaled_decomposition P g t l d (by omega) Y hY
    rw [hdlen] at he
    dsimp only [s]
    rw [secondSeparatingLayer_as_normalized]
    simpa only [a,c,s,r₁,r₂,coeff,fm,fh,show d.length=p-1 by omega,
      show d.length+2=p+1 by omega,show p-1+2=p+1 by omega,show p-1+1=p by omega,Nat.cast_add] using he
  have hcount : zeroCountLayer t d l=b+2*n := rfl
  have hsecond : secondDegreeCountLayer Y t d l=A Y*bm+2*A Y*bh+(A Y)^2*v := by
    dsimp [secondDegreeCountLayer,bm,bh,vm,vh,v,coeff]
    rw [show d.length=p-1 by omega,show p-1+2=p+1 by omega,show p-1+1=p by omega]
  rw [hdecomp,hcount,hsecond]
  have heq : a+c+s-(A Y/h)*(b+2*n)-(A Y*bm+2*A Y*bh+(A Y)^2*v)/h^2=
      (a-(A Y/h)*b-(A Y/h^2)*bm)+(c-(2*A Y/h)*n-(2*A Y/h^2)*bh)+(s-(A Y)^2/h^2*v) := by ring
  rw [heq]
  calc
    _ ≤ |a-(A Y/h)*b-(A Y/h^2)*bm|+|c-(2*A Y/h)*n-(2*A Y/h^2)*bh|+|s-(A Y)^2/h^2*v| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Cm*K*L^5/h^3+Ch*L^5/h^3+Cs*L^5/h^3 := add_le_add (add_le_add hmerger hhandle) hsep
    _ = _ := by dsimp [L];ring
end WP
