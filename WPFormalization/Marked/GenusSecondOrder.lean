import WPFormalization.Marked.FirstDegreeProof
import WPFormalization.Marked.DilatonCorrection
import WPFormalization.HigherOrder.SecondProfile

/-! The genuine first term of the separating T convolution and the genus-exchange ratio in Appendix C.1. The two three-marked spheres give the leading term; all remaining configurations have a proved second-order bound. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP
lemma W_zero_three (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : W P 0 3 Y=1 := by
  simp only [W,pow_zero,one_mul]
  change normalized P 0 [0,0,0] Y=1
  exact (initial_amplitudes P Y hY).1

lemma genus_square_to_complexity_bound (g p : ℕ) (hg : 2 ≤ g) (C z : ℝ) (hC : 0 ≤ C)
    (hz : z ≤ C/(g:ℝ)^2) : z ≤ (C*((p:ℝ)+2)^2)/(complexity g p:ℝ)^2 := by
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hsize : (complexity g p:ℝ) ≤ ((p:ℝ)+2)*(g:ℝ) := by
    have hmul : p ≤ p*g := by simpa using Nat.mul_le_mul_left p (show 1≤g by omega)
    exact_mod_cast (calc complexity g p ≤ 2*g+p := by unfold complexity;omega
                        _ ≤ 2*g+p*g := by omega
                        _ = (p+2)*g := by ring)
  have hpow := pow_le_pow_left₀ hhp.le hsize 2
  exact hz.trans ((div_le_div_iff₀ (sq_pos_of_pos hgp) (sq_pos_of_pos hhp)).2
    (by simpa only [mul_pow,mul_assoc] using mul_le_mul_of_nonneg_left hpow hC))

lemma markedSplit_T_zero_remainder (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |markedSplitGenus P g p 2 0 Y-((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y)| ≤ C/(g:ℝ)^2 := by
  obtain ⟨Cr,hCr,hratio⟩ := W_small_genus_ratio_uniform
  obtain ⟨D,hD,hW⟩ := W_finite_marking_factorial_bound P (p+1)
  let C : ℝ := (2:ℝ)^(p-2)*D*((p+1).factorial:ℝ)*Cr^2
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hC : 0<C := by dsimp [C];positivity
  obtain ⟨G,hG⟩ := exists_nat_gt (Cr+2)
  have hG2 : 2 ≤ G := by exact_mod_cast (show (2:ℝ)≤G by linarith)
  refine ⟨C,hC,G,?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := hG2.trans hg
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  let x := Cr/(g:ℝ)
  have hx : 0≤x := by dsimp [x];positivity
  have hx1 : x≤1 := by
    dsimp [x]
    apply (div_le_one hgp).2
    have hgR : (G:ℝ)≤g := by exact_mod_cast hg
    linarith
  have hzero : markedSplitTerm P g p 2 0 0 Y=0 := by
    simp only [markedSplitTerm,Nat.zero_add,W_unstable P 0 2 (by norm_num [Stable]) Y,mul_zero,zero_mul,zero_div]
  have hone : markedSplitTerm P g p 2 0 1 Y=((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y) := by
    simp only [markedSplitTerm,Nat.sub_zero,Nat.reduceAdd]
    rw [W_zero_three P Y hY,Nat.choose_one_right]
    ring
  by_cases hp2 : p=2
  · subst p
    simpa only [markedSplitGenus,Nat.reduceSub,Nat.reduceAdd,Finset.sum_range_one,hzero,Nat.cast_zero,mul_zero,zero_mul,sub_zero,abs_zero]
      using (show 0≤C/(g:ℝ)^2 by positivity)
  · have hp3 : 3 ≤ p := by omega
    have h1 : 1∈Finset.range (p-1) := Finset.mem_range.mpr (by omega)
    have he := Finset.sum_erase_add (Finset.range (p-1)) (fun s => markedSplitTerm P g p 2 0 s Y) h1
    have hres : markedSplitGenus P g p 2 0 Y-((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y)=
        ∑ s ∈ (Finset.range (p-1)).erase 1, markedSplitTerm P g p 2 0 s Y := by
      change (∑ s ∈ Finset.range (p-2+1), markedSplitTerm P g p 2 0 s Y)-_=_
      rw [show p-2+1=p-1 by omega]
      rw [hone] at he
      linarith
    rw [hres,abs_of_nonneg (show 0≤∑ s ∈ (Finset.range (p-1)).erase 1, markedSplitTerm P g p 2 0 s Y by
      apply Finset.sum_nonneg
      intro s hs
      have hs' := Finset.mem_range.mp (Finset.mem_erase.mp hs).2
      exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (W_nonneg P 0 (s+2) (by omega) Y hY))
        (W_nonneg P g (p-s) (by omega) Y hY)) (W_nonneg P g p (by omega) Y hY))]
    have hpoint (s : ℕ) (hs : s∈(Finset.range (p-1)).erase 1) :
        markedSplitTerm P g p 2 0 s Y ≤ (Nat.choose (p-2) s:ℝ)*(D*((p+1).factorial:ℝ)*x^2) := by
      have hs0 := Finset.mem_range.mp (Finset.mem_erase.mp hs).2
      have hs1 := (Finset.mem_erase.mp hs).1
      by_cases hsZ : s=0
      · subst s
        rw [hzero]
        positivity
      · have hs2 : 2 ≤ s := by omega
        have hr := hratio P g p 0 s hg2 hp (by omega) (by omega) Y hY
        simp only [Nat.sub_zero,Nat.mul_zero,Nat.zero_add] at hr
        have hr' : W P g (p-s) Y/W P g p Y ≤ x^2 := hr.trans (pow_le_pow_of_le_one hx hx1 hs2)
        have hw := hW (s+2) (by omega) (by omega) 0 Y hY
        norm_num only [Nat.zero_add,Nat.mul_zero,pow_one] at hw
        have hw0 := W_nonneg P 0 (s+2) (by omega) Y hY
        have hb : W P 0 (s+2) Y*W P g (p-s) Y/W P g p Y ≤ D*((p+1).factorial:ℝ)*x^2 := by
          calc _ = W P 0 (s+2) Y*(W P g (p-s) Y/W P g p Y) := by ring
               _ ≤ W P 0 (s+2) Y*x^2 := mul_le_mul_of_nonneg_left hr' hw0
               _ ≤ _ := mul_le_mul_of_nonneg_right hw (sq_nonneg x)
        simpa only [markedSplitTerm,Nat.sub_zero,mul_assoc,div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Nat.choose (p-2) s))
    calc _ ≤ ∑ s ∈ (Finset.range (p-1)).erase 1, (Nat.choose (p-2) s:ℝ)*(D*((p+1).factorial:ℝ)*x^2) :=
             Finset.sum_le_sum (fun s hs => hpoint s hs)
         _ ≤ ∑ s ∈ Finset.range (p-1), (Nat.choose (p-2) s:ℝ)*(D*((p+1).factorial:ℝ)*x^2) :=
             Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by intros;positivity)
         _ = _ := by
           rw [←Finset.sum_mul]
           have hc : (∑ s ∈ Finset.range (p-1), (Nat.choose (p-2) s:ℝ))=(2:ℝ)^(p-2) := by
             rw [show p-1=p-2+1 by omega]
             exact_mod_cast Nat.sum_range_choose (p-2)
           rw [hc]
           dsimp [x,C]
           rw [div_pow]
           ring
end WP
namespace WP
lemma separatingT_merge_first (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |separatingT P g p Y-2*((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y)| ≤ C/(complexity g p:ℝ)^2 := by
  obtain ⟨Cz,hCz,Gz,hzero⟩ := markedSplit_T_zero_remainder P p hp
  obtain ⟨Cp,hCp,Gp,hpos⟩ := markedSplitPositive_bound P p 2 hp (Or.inr rfl)
  refine ⟨(2*Cz+Cp)*((p:ℝ)+2)^2,by positivity,max 2 (max Gz Gp),?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgZ : Gz ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgP : Gp ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hid : separatingT P g p Y-2*((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y)=
      2*(markedSplitGenus P g p 2 0 Y-((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y))+
        markedSplitPositive P g p 2 Y := by
    rw [separatingT_eq_markedSplitConvolution P g p hp Y,
      markedSplitConvolution_eq_positive P g p 2 (by omega) hp (Or.inr rfl) Y]
    ring
  apply genus_square_to_complexity_bound g p hg2 (2*Cz+Cp) _ (by positivity)
  rw [hid]
  calc _ ≤ |2*(markedSplitGenus P g p 2 0 Y-((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y))|+
          |markedSplitPositive P g p 2 Y| := abs_add_le _ _
       _ = 2*|markedSplitGenus P g p 2 0 Y-((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y)|+
          markedSplitPositive P g p 2 Y := by
         rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
           abs_of_nonneg (markedSplitPositive_nonneg P g p 2 hg2 hp (Or.inr rfl) Y hY)]
       _ ≤ 2*(Cz/(g:ℝ)^2)+Cp/(g:ℝ)^2 := add_le_add
         (mul_le_mul_of_nonneg_left (hzero g hgZ Y hY) (by norm_num)) (hpos g hgP Y hY)
       _ = _ := by ring

lemma separatingT_first_order (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |separatingT P g p Y-2*A Y*((p:ℝ)-2)/(complexity g p:ℝ)| ≤ C/(complexity g p:ℝ)^2 := by
  obtain ⟨Ct,hCt,Gt,hT⟩ := separatingT_merge_first P p hp
  obtain ⟨Cm,hCm,Gm,hM⟩ := W_merge_prefactor_second_order P p (by omega)
  refine ⟨Ct+2*((p-2:ℕ):ℝ)*Cm,by positivity,max Gt Gm,?_⟩
  intro g hg Y hY
  have hc : ((p-2:ℕ):ℝ)=(p:ℝ)-2 := by rw [Nat.cast_sub hp];norm_num
  have hid : separatingT P g p Y-2*A Y*((p:ℝ)-2)/(complexity g p:ℝ)=
      (separatingT P g p Y-2*((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y))+
      2*((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y-A Y/(complexity g p:ℝ)) := by rw [hc];ring
  rw [hid]
  calc _ ≤ |separatingT P g p Y-2*((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y)|+
      |2*((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y-A Y/(complexity g p:ℝ))| := abs_add_le _ _
       _ = |separatingT P g p Y-2*((p-2:ℕ):ℝ)*(W P g (p-1) Y/W P g p Y)|+
         2*((p-2:ℕ):ℝ)*|W P g (p-1) Y/W P g p Y-A Y/(complexity g p:ℝ)| := by
         rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*((p-2:ℕ):ℝ))]
       _ ≤ Ct/(complexity g p:ℝ)^2+2*((p-2:ℕ):ℝ)*(Cm/(complexity g p:ℝ)^2) :=
         add_le_add (hT g ((le_max_left _ _).trans hg) Y hY)
           (mul_le_mul_of_nonneg_left (hM g ((le_max_right _ _).trans hg) Y hY) (by positivity))
       _ = _ := by ring

lemma degreeCorrection_one_alpha (p : ℕ) (hp : 2 ≤ p) (Y : ℝ) :
    degreeCorrection (1::List.replicate (p-1) 0) Y+3*A Y*((p:ℝ)-2)=HigherOrder.alpha p Y := by
  rw [degreeCorrection_single_positive 1 (p-1) (by omega) Y]
  unfold HigherOrder.alpha
  rw [Nat.cast_sub (by omega : 1≤p)]
  norm_num only [Nat.cast_one,one_pow,mul_one]
  ring

lemma marked_genus_second_order (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |W P (g-1) (p+2) Y/W P g p Y-(1-HigherOrder.alpha p Y/(complexity g p:ℝ))| ≤ C/(complexity g p:ℝ)^2 := by
  obtain ⟨Cf,hCf,Gf,hF⟩ := first_degree_all_degrees_proof P p (by omega)
  obtain ⟨Ct,hCt,Gt,hT⟩ := separatingT_first_order P p hp
  refine ⟨16*Cf+(3/2:ℝ)*Ct,by positivity,max 2 (max Gf Gt),?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgF : Gf ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgT : Gt ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hf := hF g hgF (1::List.replicate (p-1) 0) (by simp;omega) Y hY
  simp only [List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,Nat.cast_one] at hf
  norm_num only [show (1:ℝ)+1=2 by norm_num,show (2:ℝ)^4=16 by norm_num] at hf
  have hk := normalized_kdv_profile P g p (by omega) hp Y hY
  have hid : W P (g-1) (p+2) Y/W P g p Y-(1-HigherOrder.alpha p Y/(complexity g p:ℝ))=
      (profile P g (1::List.replicate (p-1) 0) Y-
        (1-degreeCorrection (1::List.replicate (p-1) 0) Y/(complexity g p:ℝ)))-
      (3/2:ℝ)*(separatingT P g p Y-2*A Y*((p:ℝ)-2)/(complexity g p:ℝ)) := by
    rw [←degreeCorrection_one_alpha p hp Y]
    have he : W P (g-1) (p+2) Y/W P g p Y=profile P g (1::List.replicate (p-1) 0) Y-(3/2:ℝ)*separatingT P g p Y := by linarith
    rw [he]
    ring
  rw [hid]
  calc _ ≤ |profile P g (1::List.replicate (p-1) 0) Y-
        (1-degreeCorrection (1::List.replicate (p-1) 0) Y/(complexity g p:ℝ))|+
      |(3/2:ℝ)*(separatingT P g p Y-2*A Y*((p:ℝ)-2)/(complexity g p:ℝ))| := abs_sub _ _
       _ = |profile P g (1::List.replicate (p-1) 0) Y-
        (1-degreeCorrection (1::List.replicate (p-1) 0) Y/(complexity g p:ℝ))|+
      (3/2:ℝ)*|separatingT P g p Y-2*A Y*((p:ℝ)-2)/(complexity g p:ℝ)| := by
        rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3/2)]
       _ ≤ (Cf*16)/(complexity g p:ℝ)^2+(3/2:ℝ)*(Ct/(complexity g p:ℝ)^2) :=
         add_le_add hf (mul_le_mul_of_nonneg_left (hT g hgT Y hY) (by norm_num))
       _ = _ := by ring
end WP
