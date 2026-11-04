import WPFormalization.HigherOrder.Triangular
import WPFormalization.HigherOrder.JetLocality
import WPFormalization.Analysis.KernelJets
import WPFormalization.Analysis.KernelAction

/-! Exact scalar identities of the defined canonical formal algorithm.
This proves its complete formal dilaton/KdV scalar rules and genus descent.
It does not prove arbitrary-coordinate profile compatibility, all-order
summability of the kernel sums, holomorphic extensions, or actual remainder
bounds. Those remain distinct paper-specific proof obligations. The actual
normalizing b sum is proved here from the entire H Taylor series. -/
set_option autoImplicit false
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma hierarchy_cusp_stable (P : PsiTheory) (Y : ℝ) (p n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k ((hierarchyJet P Y n).cusp p) = cuspCoefficient P Y p k := by
  induction n with
  | zero => simp only [show k = 0 by omega,cuspCoefficient,hierarchyJet]
  | succ n ih =>
    by_cases h : k = n+1
    · subst k;rfl
    · have hkn : k ≤ n := by omega
      simpa only [hierarchyJet,nextJet,setCoeff,PowerSeries.coeff_mk,if_neg h] using ih hkn
lemma hierarchy_genus_stable (P : PsiTheory) (Y : ℝ) (p n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k ((hierarchyJet P Y n).genus p) = genusCoefficient P Y p k := by
  induction n with
  | zero => simp only [show k = 0 by omega,genusCoefficient,hierarchyJet]
  | succ n ih =>
    by_cases h : k = n+1
    · subst k;rfl
    · have hkn : k ≤ n := by omega
      by_cases hp0 : p = 0
      · subst p
        simpa only [hierarchyJet,nextJet,ite_true,setCoeff,PowerSeries.coeff_mk,if_neg h] using ih hkn
      · by_cases hp1 : p = 1
        · subst p
          simpa only [hierarchyJet,nextJet,ite_false,ite_true,one_ne_zero,setCoeff,PowerSeries.coeff_mk,if_neg h] using ih hkn
        · simpa only [hierarchyJet,nextJet,if_neg hp0,if_neg hp1,setCoeff,PowerSeries.coeff_mk,if_neg h] using ih hkn
lemma formalProfile_stage_agree (P : PsiTheory) (Y : ℝ) (d : List ℕ) (n : ℕ) :
    AgreeBelow (n+1) (formalProfile P Y d) ((hierarchyJet P Y n).profile d) := by
  intro k hk
  simp only [formalProfile,PowerSeries.coeff_mk]
  exact (hierarchy_profile_stable P Y d n k (by omega)).symm
lemma formalCusp_stage_agree (P : PsiTheory) (Y : ℝ) (p n : ℕ) :
    AgreeBelow (n+1) (formalCusp P Y p) ((hierarchyJet P Y n).cusp p) := by
  intro k hk
  simp only [formalCusp,PowerSeries.coeff_mk]
  exact (hierarchy_cusp_stable P Y p n k (by omega)).symm
lemma formalGenus_stage_agree (P : PsiTheory) (Y : ℝ) (p n : ℕ) :
    AgreeBelow (n+1) (formalGenus P Y p) ((hierarchyJet P Y n).genus p) := by
  intro k hk
  simp only [formalGenus,PowerSeries.coeff_mk]
  exact (hierarchy_genus_stable P Y p n k (by omega)).symm
lemma descendGenus_agree {N : ℕ} {c₁ c₂ : ℕ → Series} {g₁ g₂ : Series}
    (hc : ∀ p,AgreeBelow N (c₁ p) (c₂ p)) (hg : AgreeBelow N g₁ g₂) (p : ℕ) :
    AgreeBelow N (descendGenus c₁ g₁ p) (descendGenus c₂ g₂ p) := by
  exact ((hg.shift (-1)).mul (hc (p+2))).mul (hc p).inv
lemma nextJet_genus_descent_coeff (P : PsiTheory) (Y : ℝ) (K : ℕ) (F : HierarchyJet)
    (p : ℕ) (hp : p ≤ 1) :
    PowerSeries.coeff K ((nextJet P Y K F).genus p) =
      PowerSeries.coeff K (descendGenus (nextJet P Y K F).cusp ((nextJet P Y K F).genus (p+1)) p) := by
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
  · simp only [nextJet,zero_add,ite_true,one_ne_zero,ite_false,setCoeff_same]
  · norm_num only [nextJet,one_add_one_eq_two,setCoeff_same,ite_true,ite_false]
/-- The complete formal descent identity of FE6 for p=0 and p=1. -/
lemma formalGenus_descent (P : PsiTheory) (Y : ℝ) (p : ℕ) (hp : p ≤ 1) :
    formalGenus P Y p = descendGenus (formalCusp P Y) (formalGenus P Y (p+1)) p := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
      simp only [coeff_zero_eq_constantCoeff,formalGenus_constant,descendGenus,map_mul,
        complexityShift_constant,formalCusp_constant,PowerSeries.constantCoeff_inv,inv_one,mul_one]
  | succ k =>
      have ha := descendGenus_agree (fun p => formalCusp_stage_agree P Y p (k+1))
        (formalGenus_stage_agree P Y (p+1) (k+1)) p
      have he := nextJet_genus_descent_coeff P Y (k+1) (hierarchyJet P Y k) p hp
      change PowerSeries.coeff (k+1) (formalGenus P Y p) = _
      rw [(formalGenus_stage_agree P Y p (k+1)) (k+1) (by omega),ha (k+1) (by omega)]
      exact he
lemma profileAtOrder_zero_tuple (P : PsiTheory) (Y : ℝ) (F : HierarchyJet) (K p : ℕ) :
    profileAtOrder P Y F K (List.replicate p 0) = 0 := by
  unfold profileAtOrder
  apply Finset.sum_eq_zero
  intro i hi
  have hip : i < p := by simpa only [Finset.mem_range,List.length_replicate] using hi
  have hz : (List.replicate p 0)[i]! = 0 := by
    simp only [List.getElem!_eq_getElem?_getD,List.getElem?_replicate,hip,ite_true,Option.getD_some]
  rw [hz]
  simp only [Finset.range_zero,Finset.sum_empty]
/-- The zero-degree normalization of FE5 holds at every order. -/
lemma formalProfile_zero_tuple (P : PsiTheory) (Y : ℝ) (p : ℕ) :
    formalProfile P Y (List.replicate p 0) = 1 := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp only [coeff_zero_eq_constantCoeff,formalProfile_constant,map_one]
  | succ k =>
      simp only [formalProfile,PowerSeries.coeff_mk]
      change PowerSeries.coeff (k+1)
        (setCoeff ((hierarchyJet P Y k).profile (List.replicate p 0)) (k+1)
          (profileAtOrder P Y (hierarchyJet P Y k) (k+1) (List.replicate p 0))) = _
      rw [setCoeff_same,profileAtOrder_zero_tuple]
      simp only [PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false]
lemma ratioSeries_coeff_congr (Y : ℝ) (F G : HierarchyJet) (K p j s : ℕ)
    (hpos : 0 < 2*j+s)
    (hc : ∀ q,AgreeBelow K (F.cusp q) (G.cusp q))
    (hg : ∀ q,AgreeBelow K (F.genus q) (G.genus q)) :
    PowerSeries.coeff K (ratioSeries Y F p j s) = PowerSeries.coeff K (ratioSeries Y G p j s) := by
  let r := 2*j+s
  have hpref : constantCoeff ((C (A Y)*PowerSeries.X)^r) = 0 := by
    change constantCoeff ((C (A Y)*PowerSeries.X)^(2*j+s)) = 0
    simp only [map_pow,map_mul,constantCoeff_C,constantCoeff_X,mul_zero,zero_pow hpos.ne']
  have hcusps : AgreeBelow K
      (∏ a ∈ Finset.range r,complexityShift (r-a) (F.cusp (p-s+a))*(1-C ((r-a:ℕ):ℝ)*PowerSeries.X)⁻¹)
      (∏ a ∈ Finset.range r,complexityShift (r-a) (G.cusp (p-s+a))*(1-C ((r-a:ℕ):ℝ)*PowerSeries.X)⁻¹) := by
    apply AgreeBelow.prod
    intro a ha
    exact ((hc (p-s+a)).shift (r-a)).mul (AgreeBelow.refl K _)
  have hgenus : AgreeBelow K (∏ b ∈ Finset.range j,F.genus (p+2*b))
      (∏ b ∈ Finset.range j,G.genus (p+2*b)) := by
    apply AgreeBelow.prod
    intro b hb
    exact hg _
  unfold ratioSeries
  dsimp only
  rw [mul_assoc,mul_assoc]
  exact coeff_mul_eq_of_zero_constant hpref (hcusps.mul hgenus)
lemma genusSeries_coeff_congr (P : PsiTheory) (Y : ℝ) (F G : HierarchyJet)
    (f g : List ℕ → Series) (K p : ℕ)
    (hprof : ∀ d,AgreeBelow (K+1) (f d) (g d))
    (hc : ∀ q,AgreeBelow K (F.cusp q) (G.cusp q))
    (hg : ∀ q,AgreeBelow K (F.genus q) (G.genus q)) :
    PowerSeries.coeff K (genusSeries P Y F f K p) =
      PowerSeries.coeff K (genusSeries P Y G g K p) := by
  let U (H : HierarchyJet) : Series :=
    ∑ j ∈ Finset.range (K+1), ∑ s ∈ Finset.range (p-1),
      if Stable j (s+2) ∧ 1 ≤ 2*j+s ∧ 2*j+s ≤ K then
        C ((Nat.choose (p-2) s:ℝ)*smallW P Y j (List.replicate (s+2) 0))*ratioSeries Y H p j s else 0
  have hsum : PowerSeries.coeff K (U F) = PowerSeries.coeff K (U G) := by
    dsimp only [U]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro s hs
    by_cases h : Stable j (s+2) ∧ 1 ≤ 2*j+s ∧ 2*j+s ≤ K
    · simp only [if_pos h,PowerSeries.coeff_C_mul]
      rw [ratioSeries_coeff_congr Y F G K p j s (by omega) hc hg]
    · simp only [if_neg h]
  change PowerSeries.coeff K (f (1::List.replicate (p-1) 0)-C 3*U F) =
    PowerSeries.coeff K (g (1::List.replicate (p-1) 0)-C 3*U G)
  rw [map_sub,map_sub,hprof _ K (by omega),PowerSeries.coeff_C_mul,PowerSeries.coeff_C_mul,hsum]

lemma formalGenus_kdv_coefficient (P : PsiTheory) (Y : ℝ) (p : ℕ) (hp : 2 ≤ p) (K : ℕ) :
    PowerSeries.coeff K (formalGenus P Y p) =
      PowerSeries.coeff K (genusSeries P Y
        ⟨formalProfile P Y,formalCusp P Y,formalGenus P Y⟩ (formalProfile P Y) K p) := by
  cases K with
  | zero =>
      have he : ∀ j s,¬ (Stable j (s+2) ∧ 1 ≤ 2*j+s ∧ 2*j+s ≤ 0) := by intro j s;omega
      let F : HierarchyJet := ⟨formalProfile P Y,formalCusp P Y,formalGenus P Y⟩
      have hsum : (∑ j ∈ Finset.range (0+1),∑ s ∈ Finset.range (p-1),
          if Stable j (s+2) ∧ 1 ≤ 2*j+s ∧ 2*j+s ≤ 0 then
            C ((Nat.choose (p-2) s:ℝ)*smallW P Y j (List.replicate (s+2) 0))*ratioSeries Y F p j s
          else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        apply Finset.sum_eq_zero
        intro s hs
        exact if_neg (he j s)
      change PowerSeries.coeff 0 (formalGenus P Y p) =
        PowerSeries.coeff 0 (genusSeries P Y F (formalProfile P Y) 0 p)
      rw [genusSeries,hsum,mul_zero,sub_zero]
      simp only [coeff_zero_eq_constantCoeff,formalGenus_constant,formalProfile_constant]
  | succ k =>
      have hp0 : p ≠ 0 := by omega
      have hp1 : p ≠ 1 := by omega
      have hcan := genusSeries_coeff_congr P Y
        ⟨formalProfile P Y,formalCusp P Y,formalGenus P Y⟩ (hierarchyJet P Y k)
        (formalProfile P Y) ((hierarchyJet P Y (k+1)).profile) (k+1) p
        (fun d => formalProfile_stage_agree P Y d (k+1))
        (fun q => formalCusp_stage_agree P Y q k) (fun q => formalGenus_stage_agree P Y q k)
      have hdef : PowerSeries.coeff (k+1) ((hierarchyJet P Y (k+1)).genus p) =
          PowerSeries.coeff (k+1) (genusSeries P Y (hierarchyJet P Y k)
            ((hierarchyJet P Y (k+1)).profile) (k+1) p) := by
        simp only [hierarchyJet,nextJet,if_neg hp0,if_neg hp1,setCoeff_same]
      rw [(formalGenus_stage_agree P Y p (k+1)) (k+1) (by omega)]
      exact hdef.trans hcan.symm
lemma bCoeff_succ_hasSum (Y : ℝ) : HasSum (fun d => bCoeff Y (d+1)) (A Y) := by
  have hs := Complex.hasSum_taylorSeries_of_entire (WP.barH_differentiable Y) 0 1
  have hsc : HasSum (fun n => WP.coeff (barH Y) n) (barH Y 1) := by
    convert! hs using 1
    ext n
    simp only [WP.coeff,sub_zero,one_pow,smul_eq_mul,mul_one]
    ring
  have hr : HasSum (fun n => WP.realCoeff (barH Y) n) (barH Y 1).re := by
    simpa only [WP.realCoeff,Complex.reCLM_apply] using hsc.mapL Complex.reCLM
  convert! hr.div_const 3 using 1 <;> simp [bCoeff,A]
lemma A_ne_zero_closed (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) : A Y ≠ 0 := by
  by_cases he : Y = y₀
  · subst Y
    norm_num [A,barH]
  · have hi : Y ∈ Set.Ico 0 y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
    intro hA
    have hI := WP.Analysis.normalized_kernel_action Y hi
    rw [hA,zero_mul,zero_mul] at hI
    have hp := mul_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)) (WP.action_pos Y hi)
    linarith
lemma cuspSeries_agree {N : ℕ} {f g : List ℕ → Series} (Y : ℝ) (p : ℕ)
    (h : ∀ d,AgreeBelow N (f d) (g d)) :
    AgreeBelow N (cuspSeries Y f p) (cuspSeries Y g p) := by
  apply (AgreeBelow.refl N (C (A Y)⁻¹)).mul
  apply AgreeBelow.coefficientSum
  intro d
  exact (AgreeBelow.refl N (C (bCoeff Y (d+1)))).mul ((h _).shift (-1))
lemma formalCusp_rhs_constant (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (p : ℕ) :
    constantCoeff (cuspSeries Y (formalProfile P Y) p) = 1 := by
  have hc : constantCoeff (coefficientSum (fun d =>
      C (bCoeff Y (d+1))*complexityShift (-1) (formalProfile P Y ((d+1)::List.replicate p 0)))) = A Y := by
    rw [← coeff_zero_eq_constantCoeff,coefficientSum_coeff]
    simpa only [coeff_zero_eq_constantCoeff,map_mul,constantCoeff_C,complexityShift_constant,
      formalProfile_constant,mul_one] using (bCoeff_succ_hasSum Y).tsum_eq
  unfold cuspSeries
  simp only [map_mul,PowerSeries.constantCoeff_inv,constantCoeff_C,hc]
  exact inv_mul_cancel₀ (A_ne_zero_closed Y hY)
/-- The complete formal dilaton scalar identity of FE5, for the canonical hierarchy. -/
lemma formalCusp_recursion (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (p : ℕ) :
    formalCusp P Y p = cuspSeries Y (formalProfile P Y) p := by
  apply PowerSeries.ext
  intro K
  cases K with
  | zero => simp only [coeff_zero_eq_constantCoeff,formalCusp_constant,formalCusp_rhs_constant P Y hY]
  | succ k =>
      have hc := cuspSeries_agree Y p (fun d => formalProfile_stage_agree P Y d (k+1))
      have he : PowerSeries.coeff (k+1) ((hierarchyJet P Y (k+1)).cusp p) =
          PowerSeries.coeff (k+1) (cuspSeries Y (hierarchyJet P Y (k+1)).profile p) := by
        simp only [hierarchyJet,nextJet,setCoeff_same]
      rw [(formalCusp_stage_agree P Y p (k+1)) (k+1) (by omega)]
      exact he.trans (hc (k+1) (by omega)).symm

end WP.HigherOrder
