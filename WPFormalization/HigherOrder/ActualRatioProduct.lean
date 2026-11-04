import WPFormalization.Statements.Coefficients
import WPFormalization.Marked.Positivity
import WPFormalization.HigherOrder.HierarchyIdentities
import Mathlib
/-! Exact finite large-component ratios for Appendix C.14. Every actual cusp
and genus factor retains its shifted complexity. Genuine small-weight geometry
proves child stability, and the normalized finite core agrees with the formal
factor pattern without evaluating an infinite hierarchy. Actual separating
summands are factored into the small amplitude, large profile, and this ratio. -/
noncomputable section
namespace WP.HigherOrder
open Set

lemma actualRatio_prod_forward (f:ℕ→ℝ)(n:ℕ)(hf:∀k≤n,f k≠0) :
    (∏i∈Finset.range n,f (i+1)/f i)=f n/f 0 := by
  induction n with
  | zero=>simp [hf 0 (by omega)]
  | succ n ih=>
    rw [Finset.prod_range_succ,ih (fun k hk=>hf k (by omega))]
    field_simp [hf n (by omega),hf 0 (by omega)]

lemma actualRatio_prod_backward (f:ℕ→ℝ)(n:ℕ)(hf:∀k≤n,f k≠0) :
    (∏i∈Finset.range n,f i/f (i+1))=f 0/f n := by
  induction n with
  | zero=>simp [hf 0 (by omega)]
  | succ n ih=>
    rw [Finset.prod_range_succ,ih (fun k hk=>hf k (by omega))]
    field_simp [hf n (by omega),hf (n+1) (by omega)]

lemma cuspCorrection_exact_ratio (P:PsiTheory)(g p:ℕ)(hs:Stable g p)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀) :
    A Y*cuspCorrection P g p Y/(complexity g p:ℝ)=W P g p Y/W P g (p+1) Y := by
  have hh:complexity g p≠0 := by unfold Stable complexity at *;omega
  have hhR:(complexity g p:ℝ)≠0 := by exact_mod_cast hh
  have ha:=A_ne_zero_closed Y hY
  have he:A Y*((complexity g p:ℝ)/A Y)/(complexity g p:ℝ)=1 := by field_simp
  unfold cuspCorrection
  calc
    _=(A Y*((complexity g p:ℝ)/A Y)/(complexity g p:ℝ))*(W P g p Y/W P g (p+1) Y) := by ring
    _=_ := by rw [he,one_mul]

lemma cuspCorrection_exact_product (P:PsiTheory)(g q n:ℕ)(hq:1≤q)(hs:Stable g q)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀) :
    (∏a∈Finset.range n,A Y*cuspCorrection P g (q+a) Y/(complexity g (q+a):ℝ))=
      W P g q Y/W P g (q+n) Y := by
  have hn:∀a≤n,W P g (q+a) Y≠0 := by
    intro a ha
    exact (W_pos P g (q+a) (by omega) (by unfold Stable at *;omega) Y hY).ne'
  have he:=actualRatio_prod_backward (fun a=>W P g (q+a) Y) n hn
  calc
    _=(∏a∈Finset.range n,W P g (q+a) Y/W P g (q+(a+1)) Y) := by
      apply Finset.prod_congr rfl
      intro a ha
      simpa only [Nat.add_assoc] using cuspCorrection_exact_ratio P g (q+a)
        (by unfold Stable at *;omega) Y hY
    _=_ := by simpa only [Nat.add_zero] using he

lemma genusCorrection_exact_product (P:PsiTheory)(g p j:ℕ)(hj:j≤g)(hp:1≤p)
    (hs:Stable g p)(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀) :
    (∏b∈Finset.range j,genusCorrection P (g-b) (p+2*b) Y)=
      W P (g-j) (p+2*j) Y/W P g p Y := by
  have hn:∀b≤j,W P (g-b) (p+2*b) Y≠0 := by
    intro b hb
    exact (W_pos P (g-b) (p+2*b) (by omega)
      (by unfold Stable at *;omega) Y hY).ne'
  have he:=actualRatio_prod_forward (fun b=>W P (g-b) (p+2*b) Y) j hn
  calc
    _=(∏b∈Finset.range j,W P (g-(b+1)) (p+2*(b+1)) Y/W P (g-b) (p+2*b) Y) := by
      apply Finset.prod_congr rfl
      intro b hb
      have hb':b<j:=Finset.mem_range.mp hb
      rw [genusCorrection_of_pos P (g-b) _ Y (by omega)]
      congr 2
    _=_ := by simpa using he

lemma large_component_ratio_exact_product (P:PsiTheory)(g p j s:ℕ)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(hj:j≤g)(hs:s<p)
    (hstable:Stable (g-j) (p-s)) :
    W P (g-j) (p-s) Y/W P g p Y=
      (∏a∈Finset.range (2*j+s),
        A Y*cuspCorrection P (g-j) (p-s+a) Y/
          ((complexity g p:ℝ)-(2*j+s:ℕ)+a))*
      ∏b∈Finset.range j,genusCorrection P (g-b) (p+2*b) Y := by
  have hp:1≤p:=by omega
  have hparent:Stable g p:=by unfold Stable at *;omega
  have hq:1≤p-s:=by omega
  have hlen:p-s+(2*j+s)=p+2*j:=by omega
  have hmid:W P (g-j) (p+2*j) Y≠0 :=
    (W_pos P (g-j) (p+2*j) (by omega) (by unfold Stable at *;omega) Y hY).ne'
  have hden:W P g p Y≠0 :=(W_pos P g p hp hparent Y hY).ne'
  have hshift (a:ℕ):(complexity (g-j) (p-s+a):ℝ)=
      (complexity g p:ℝ)-(2*j+s:ℕ)+a := by
    have he:complexity (g-j) (p-s+a)+(2*j+s)=complexity g p+a := by
      unfold Stable complexity at *
      omega
    have heR:(complexity (g-j) (p-s+a):ℝ)+((2*j+s:ℕ):ℝ)=(complexity g p:ℝ)+a := by exact_mod_cast he
    linarith
  have hc:=cuspCorrection_exact_product P (g-j) (p-s) (2*j+s) hq hstable Y hY
  rw [hlen] at hc
  have hg:=genusCorrection_exact_product P g p j hj hp hparent Y hY
  simp_rw [←hshift]
  rw [hc,hg]
  field_simp

lemma small_weight_split_child_valid (g p j s L:ℕ)(S:ℝ)
    (hp:1≤p)(hL:1≤L)(hstable:Stable g p)
    (hS:(p:ℝ)+2*L≤S)(hsmall:S^2/(complexity g p:ℝ)<1)
    (hr:2*j+s≤L)(hs:s<p) : j≤g ∧ Stable (g-j) (p-s) := by
  have hh:0<(complexity g p:ℝ) := by
    have hn:0<complexity g p := by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have heq:(complexity g p:ℝ)=2*(g:ℝ)+p-2 := by
    unfold complexity
    rw [Nat.cast_sub (by unfold Stable at *;omega)]
    push_cast
    ring
  have hpR:(1:ℝ)≤p := by exact_mod_cast hp
  have hLR:(1:ℝ)≤L := by exact_mod_cast hL
  have hS1:1≤S := by linarith
  have hSS:S≤S^2 := by nlinarith
  have hbig:S^2<(complexity g p:ℝ) := (div_lt_one hh).mp hsmall
  have hgR:(L:ℝ)+1<(g:ℝ) := by rw [heq] at hbig;nlinarith
  have hg:L+1<g := by exact_mod_cast hgR
  constructor
  · omega
  · unfold Stable
    omega

lemma large_component_ratio_exact_product_small_weight (P:PsiTheory)(g p j s L:ℕ)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(S:ℝ)(hp:1≤p)(hL:1≤L)(hstable:Stable g p)
    (hS:(p:ℝ)+2*L≤S)(hsmall:S^2/(complexity g p:ℝ)<1)
    (hr:2*j+s≤L)(hs:s<p) :
    W P (g-j) (p-s) Y/W P g p Y=
      (∏a∈Finset.range (2*j+s),
        A Y*cuspCorrection P (g-j) (p-s+a) Y/
          ((complexity g p:ℝ)-(2*j+s:ℕ)+a))*
      ∏b∈Finset.range j,genusCorrection P (g-b) (p+2*b) Y := by
  obtain ⟨hj,hc⟩:=small_weight_split_child_valid g p j s L S hp hL hstable hS hsmall hr hs
  exact large_component_ratio_exact_product P g p j s Y hY hj hs hc

lemma actualRatio_linear_shift_factor (A₀ C₀ h:ℝ)(r a:ℕ)(ha:a≤r)
    (hh:h≠0)(hd:h-(r:ℝ)+a≠0) :
    A₀*C₀/(h-(r:ℝ)+a)=(A₀/h)*(C₀/(1-((r-a:ℕ):ℝ)/h)) := by
  have hcast:((r-a:ℕ):ℝ)=(r:ℝ)-a := by exact_mod_cast Nat.cast_sub ha (R:=ℝ)
  have he:1-((r-a:ℕ):ℝ)/h=(h-(r:ℝ)+a)/h := by
    rw [hcast]
    field_simp
    ring
  rw [he]
  field_simp

/-- Actual finite core corresponding to ratioCoreSeries, evaluated only as
actual cusp/genus factors, never as a convergent formal hierarchy. -/
def actualLargeRatioCore (P:PsiTheory)(g p j s:ℕ)(Y:ℝ):ℝ :=
  (∏a∈Finset.range (2*j+s),cuspCorrection P (g-j) (p-s+a) Y/
    (1-(((2*j+s-a:ℕ):ℝ)/(complexity g p:ℝ))))*
    ∏b∈Finset.range j,genusCorrection P (g-b) (p+2*b) Y

lemma large_component_ratio_exact_core (P:PsiTheory)(g p j s:ℕ)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(hj:j≤g)(hs:s<p)
    (hstable:Stable (g-j) (p-s)) :
    W P (g-j) (p-s) Y/W P g p Y=
      (A Y/(complexity g p:ℝ))^(2*j+s)*actualLargeRatioCore P g p j s Y := by
  have hparent:Stable g p := by unfold Stable at *;omega
  have hh:(complexity g p:ℝ)≠0 := by
    have hn:complexity g p≠0 := by unfold Stable complexity at *;omega
    exact_mod_cast hn
  have heprod:(∏a∈Finset.range (2*j+s),A Y*cuspCorrection P (g-j) (p-s+a) Y/
      ((complexity g p:ℝ)-(2*j+s:ℕ)+a))=
      (A Y/(complexity g p:ℝ))^(2*j+s)*
        ∏a∈Finset.range (2*j+s),cuspCorrection P (g-j) (p-s+a) Y/
          (1-(((2*j+s-a:ℕ):ℝ)/(complexity g p:ℝ))) := by
    calc
      _=(∏a∈Finset.range (2*j+s),(A Y/(complexity g p:ℝ))*
        (cuspCorrection P (g-j) (p-s+a) Y/(1-(((2*j+s-a:ℕ):ℝ)/(complexity g p:ℝ))))) := by
        apply Finset.prod_congr rfl
        intro a ha
        have har:a≤2*j+s := (Finset.mem_range.mp ha).le
        have hn:complexity (g-j) (p-s+a)≠0 := by unfold Stable complexity at *;omega
        have he:complexity (g-j) (p-s+a)+(2*j+s)=complexity g p+a := by unfold Stable complexity at *;omega
        have heR:(complexity (g-j) (p-s+a):ℝ)+((2*j+s:ℕ):ℝ)=(complexity g p:ℝ)+a := by exact_mod_cast he
        have hc:(complexity g p:ℝ)-(2*j+s:ℕ)+a=(complexity (g-j) (p-s+a):ℝ) := by linarith
        have hden:(complexity g p:ℝ)-(2*j+s:ℕ)+a≠0 := by rw [hc];exact_mod_cast hn
        exact actualRatio_linear_shift_factor _ _ _ _ _ har hh hden
      _=_ := by rw [Finset.prod_mul_distrib];simp only [Finset.prod_const,Finset.card_range]
  rw [large_component_ratio_exact_product P g p j s Y hY hj hs hstable,heprod]
  unfold actualLargeRatioCore
  ring

lemma large_component_ratio_exact_core_small_weight (P:PsiTheory)(g p j s L:ℕ)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(S:ℝ)(hp:1≤p)(hL:1≤L)(hstable:Stable g p)
    (hS:(p:ℝ)+2*L≤S)(hsmall:S^2/(complexity g p:ℝ)<1)
    (hr:2*j+s≤L)(hs:s<p) :
    W P (g-j) (p-s) Y/W P g p Y=
      (A Y/(complexity g p:ℝ))^(2*j+s)*actualLargeRatioCore P g p j s Y := by
  obtain ⟨hj,hc⟩:=small_weight_split_child_valid g p j s L S hp hL hstable hS hsmall hr hs
  exact large_component_ratio_exact_core P g p j s Y hY hj hs hc

lemma actual_split_large_component_factor (P:PsiTheory)(g p j s:ℕ)
    (small large:List ℕ)(hlen:large.length=p-s)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(hj:j≤g)(hs:s<p)
    (hstable:Stable (g-j) (p-s)) :
    (4:ℝ)^g*normalized P j small Y*normalized P (g-j) large Y/W P g p Y=
      smallW P Y j small*profile P (g-j) large Y*
        ((A Y/(complexity g p:ℝ))^(2*j+s)*actualLargeRatioCore P g p j s Y) := by
  rw [←large_component_ratio_exact_core P g p j s Y hY hj hs hstable]
  have hn:normalized P (g-j) large Y=
      normalized P (g-j) (List.replicate (p-s) 0) Y*profile P (g-j) large Y := by
    have hb:normalized P (g-j) (List.replicate (p-s) 0) Y≠0 :=
      (normalized_pos_valid_nonempty P (g-j) _ (by simp;omega)
        (by simpa only [List.length_replicate] using hstable) (by simp) Y hY).ne'
    unfold profile
    rw [hlen]
    exact (mul_div_cancel₀ _ hb).symm
  have hp:(4:ℝ)^j*(4:ℝ)^(g-j)=(4:ℝ)^g := by rw [←pow_add,Nat.add_sub_of_le hj]
  rw [hn]
  unfold smallW W
  rw [←hp]
  ring

end WP.HigherOrder
