import WPFormalization.Marked.GenusExtensions
/-! Uniform second-order merging and handle prefactors from the genuine cusp/genus estimates.
For one marking, the required zero-marking intermediate denominator is proved positive
in the eventual genus range from the actual cusp estimate. -/
noncomputable section
namespace WP.Analysis
lemma first_order_cusp_to_second_order (x a h g c b k : ℝ)
    (hh : 2 ≤ h) (hg : 0 < g) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hkg : h ≤ k*g) (ha : |a| ≤ b)
    (hx : |(h-1)*x-a| ≤ c/g) :
    |x-a/h| ≤ (2*c*k+2*b)/h^2 := by
  have hhp : 0<h := by linarith
  have hhm : 0<h-1 := by linarith
  have h2 : 0<h^2 := sq_pos_of_pos hhp
  have hfact : x-a/h = ((h-1)*x-a)/(h-1) + a/(h*(h-1)) := by
    field_simp;ring
  have hh2 : h ≤ 2*(h-1) := by linarith
  have hs : h^2 ≤ 2*k*g*(h-1) := by
    calc h^2 = h*h := by ring
         _ ≤ (k*g)*(2*(h-1)) := mul_le_mul hkg hh2 hhp.le (by linarith)
         _ = _ := by ring
  have hfirst : (c/g)/(h-1) ≤ 2*c*k/h^2 := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hg hhm) h2).2
    nlinarith [mul_le_mul_of_nonneg_left hs hc]
  have hsecond : b/(h*(h-1)) ≤ 2*b/h^2 := by
    apply (div_le_div_iff₀ (mul_pos hhp hhm) h2).2
    have hi : h^2 ≤ 2*h*(h-1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hi hb]
  rw [hfact]
  calc _ ≤ |((h-1)*x-a)/(h-1)|+|a/(h*(h-1))| := abs_add_le _ _
       _ = |(h-1)*x-a|/(h-1)+|a|/(h*(h-1)) := by
         rw [abs_div,abs_of_pos hhm,abs_div,abs_of_pos (mul_pos hhp hhm)]
       _ ≤ (c/g)/(h-1)+b/(h*(h-1)) :=
         add_le_add (div_le_div_of_nonneg_right hx hhm.le)
           (div_le_div_of_nonneg_right ha (mul_pos hhp hhm).le)
       _ ≤ 2*c*k/h^2+2*b/h^2 := add_le_add hfirst hsecond
       _ = _ := by ring

lemma product_prefactor_second_order (x r a h g c d b k : ℝ)
    (hh : 1 ≤ h) (hg : 0<g) (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hkg : h ≤ k*g) (ha : |a| ≤ b)
    (hx : |x-a/h| ≤ c/h^2) (hr : |r-1| ≤ d/g) :
    |r*x-a/h| ≤ (c+d*k*(b+c))/h^2 := by
  have hhp : 0<h := by linarith
  have h2 : 0<h^2 := sq_pos_of_pos hhp
  have hxabs : |x| ≤ (b+c)/h := by
    calc |x| = |(x-a/h)+a/h| := by congr 1;ring
         _ ≤ |x-a/h|+|a/h| := abs_add_le _ _
         _ ≤ c/h^2+b/h := add_le_add hx (by rw [abs_div,abs_of_pos hhp];exact div_le_div_of_nonneg_right ha hhp.le)
         _ ≤ c/h+b/h := by
           apply add_le_add_left
           apply (div_le_div_iff₀ h2 hhp).2
           have hs : h ≤ h^2 := by nlinarith
           exact mul_le_mul_of_nonneg_left hs hc
         _ = _ := by ring
  have hfirst : d/g*((b+c)/h) ≤ d*k*(b+c)/h^2 := by
    have hprod : d*(b+c)*h ≤ d*(b+c)*(k*g) := mul_le_mul_of_nonneg_left hkg (by positivity)
    rw [div_mul_div_comm]
    apply (div_le_div_iff₀ (mul_pos hg hhp) h2).2
    nlinarith [mul_le_mul_of_nonneg_right hprod hhp.le]
  calc |r*x-a/h| = |(r-1)*x+(x-a/h)| := by congr 1;ring
       _ ≤ |(r-1)*x|+|x-a/h| := abs_add_le _ _
       _ = |r-1| * |x|+|x-a/h| := by rw [abs_mul]
       _ ≤ d/g*((b+c)/h)+c/h^2 :=
         add_le_add (mul_le_mul hr hxabs (abs_nonneg _) (by positivity)) hx
       _ ≤ d*k*(b+c)/h^2+c/h^2 := add_le_add_left hfirst _
       _ = _ := by ring
end WP.Analysis

namespace WP
lemma complexity_le_genus_multiple (g p : ℕ) (hg : 1 ≤ g) :
    complexity g p ≤ (p+2)*g := by
  have hpg : p ≤ p*g := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left p hg
  calc complexity g p ≤ 2*g+p := Nat.sub_le _ _
       _ ≤ 2*g+p*g := Nat.add_le_add_left hpg _
       _ = _ := by ring

lemma W_eventually_pos_all (P : PsiTheory) (p : ℕ) :
    ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Set.Icc (0:ℝ) y₀, 0 < W P g p Y := by
  obtain ⟨a,ha,hA⟩ := singleMarking_A_uniform_lower
  obtain ⟨C,hC,G,hcusp⟩ := marked_cusp_all_proof P p
  obtain ⟨N,hN⟩ := exists_nat_gt (C/a)
  refine ⟨2+G+N,?_⟩
  intro g hg Y hY
  have hg₂ : 2 ≤ g := by omega
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hNg : (N:ℝ) ≤ g := by exact_mod_cast (show N≤g by omega)
  have he : C/(g:ℝ)<a := by
    apply (div_lt_iff₀ hgp).2
    have hi := (div_lt_iff₀ ha).mp hN
    nlinarith
  have hc := hcusp g (by omega) Y hY
  have hx : 0 < (complexity g p:ℝ)*W P g p Y/W P g (p+1) Y := by
    have hi := (abs_le.mp hc).1
    have := hA Y hY
    linarith
  have hw : 0<W P g (p+1) Y := W_pos P g (p+1) (by omega) (by unfold Stable;omega) Y hY
  have hh : 0<(complexity g p:ℝ) := by
    exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hm := (div_pos_iff_of_pos_right hw).mp hx
  exact (mul_pos_iff_of_pos_left hh).mp hm

lemma W_merge_prefactor_second_order (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Set.Icc (0:ℝ) y₀,
      |W P g (p-1) Y/W P g p Y-A Y/(complexity g p:ℝ)| ≤
        C/(complexity g p:ℝ)^2 := by
  obtain ⟨c,hc,G,hcusp⟩ := marked_cusp_all_proof P (p-1)
  obtain ⟨b,hb,hB⟩ := genusExtension_A_uniform_upper
  have hk : 0<((p:ℝ)+2) := by positivity
  refine ⟨2*c*((p:ℝ)+2)+2*b,by positivity,2+G,?_⟩
  intro g hg Y hY
  have hg₂ : 2≤g := by omega
  have hg₁ : 1≤g := by omega
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hh : 2≤(complexity g p:ℝ) := by
    exact_mod_cast (show 2≤complexity g p by unfold complexity;omega)
  have hkbound : (complexity g p:ℝ) ≤ ((p:ℝ)+2)*g := by
    exact_mod_cast complexity_le_genus_multiple g p hg₁
  have hA : |A Y|≤b := by
    have hpos : 0<A Y := div_pos (Analysis.barH_one_re_pos Y hY) (by norm_num)
    rw [abs_of_pos hpos]
    exact hB Y hY
  have hshift : (complexity g (p-1):ℝ)=(complexity g p:ℝ)-1 := by
    have hn : complexity g p=complexity g (p-1)+1 := by unfold complexity;omega
    rw [hn,Nat.cast_add,Nat.cast_one]
    ring
  have hcusp' := hcusp g (by omega) Y hY
  rw [show p-1+1=p by omega,hshift] at hcusp'
  have he : |((complexity g p:ℝ)-1)*(W P g (p-1) Y/W P g p Y)-A Y|≤c/g := by
    simpa only [mul_div_assoc] using hcusp'
  exact Analysis.first_order_cusp_to_second_order _ _ _ _ c b ((p:ℝ)+2)
    hh hgp hc.le hb.le hkbound hA he

lemma W_handle_prefactor_second_order (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Set.Icc (0:ℝ) y₀,
      |W P (g-1) (p+1) Y/W P g p Y-A Y/(complexity g p:ℝ)| ≤
        C/(complexity g p:ℝ)^2 := by
  obtain ⟨c,hc,Gm,hmerge⟩ := W_merge_prefactor_second_order P p hp
  obtain ⟨d,hd,Gr,hgenus⟩ := marked_genus_all_proof P (p-1)
  obtain ⟨b,hb,hB⟩ := genusExtension_A_uniform_upper
  obtain ⟨Gp,hpos⟩ := W_eventually_pos_all P (p-1)
  refine ⟨c+d*((p:ℝ)+2)*(b+c),by positivity,2+Gm+Gr+Gp,?_⟩
  intro g hg Y hY
  have hh : 1≤(complexity g p:ℝ) := by
    exact_mod_cast (show 1≤complexity g p by unfold complexity;omega)
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hkbound : (complexity g p:ℝ)≤((p:ℝ)+2)*g := by
    exact_mod_cast complexity_le_genus_multiple g p (by omega)
  have hA : |A Y|≤b := by
    have hpos : 0<A Y := div_pos (Analysis.barH_one_re_pos Y hY) (by norm_num)
    rw [abs_of_pos hpos]
    exact hB Y hY
  have hm := hmerge g (by omega) Y hY
  have hr := hgenus g (by omega) Y hY
  rw [show p-1+2=p+1 by omega] at hr
  have hpz : W P g (p-1) Y≠0 := (hpos g (by omega) Y hY).ne'
  have heq : W P (g-1) (p+1) Y/W P g p Y=
      (W P (g-1) (p+1) Y/W P g (p-1) Y)*(W P g (p-1) Y/W P g p Y) := by
    field_simp
  rw [heq]
  exact Analysis.product_prefactor_second_order _ _ _ _ _ c d b ((p:ℝ)+2)
    hh hgp hc.le hd.le hb.le hkbound hA hm hr
end WP
