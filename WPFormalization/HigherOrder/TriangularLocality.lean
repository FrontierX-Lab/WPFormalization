import WPFormalization.HigherOrder.HierarchyIdentities

/-! Exact finite-order locality for the actual triangular hierarchy. A separating loss r saves precisely r coefficients. The completed formal profile obeys its prescribed canonical-path coefficient rule; no arbitrary-path compatibility or analytic remainder is assumed. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

def ratioCoreSeries (F : HierarchyJet) (p j s : ℕ) : Series :=
  let r:=2*j+s
  (∏a∈Finset.range r,complexityShift (r-a) (F.cusp (p-s+a))*
    (1-C ((r-a:ℕ):ℝ)*PowerSeries.X)⁻¹)*∏b∈Finset.range j,F.genus (p+2*b)

lemma ratioSeries_mul_coeff (Y : ℝ) (F : HierarchyJet) (p j s K : ℕ) (u : Series) :
    PowerSeries.coeff K (ratioSeries Y F p j s*u)=
      if 2*j+s≤K then (A Y)^(2*j+s)*PowerSeries.coeff (K-(2*j+s))
        (ratioCoreSeries F p j s*u) else 0 := by
  unfold ratioSeries
  simp only [mul_pow,←map_pow,mul_assoc]
  rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul']
  split_ifs <;>simp [ratioCoreSeries,mul_assoc]

lemma ratioSeries_coeff (Y : ℝ) (F : HierarchyJet) (p j s K : ℕ) :
    PowerSeries.coeff K (ratioSeries Y F p j s)=
      if 2*j+s≤K then (A Y)^(2*j+s)*PowerSeries.coeff (K-(2*j+s))
        (ratioCoreSeries F p j s) else 0 := by
  simpa only [mul_one] using ratioSeries_mul_coeff Y F p j s K 1

lemma ratioCoreSeries_agree {N : ℕ} (F G : HierarchyJet)
    (hc : ∀p,AgreeBelow N (F.cusp p) (G.cusp p))
    (hg : ∀p,AgreeBelow N (F.genus p) (G.genus p)) (p j s : ℕ) :
    AgreeBelow N (ratioCoreSeries F p j s) (ratioCoreSeries G p j s) := by
  apply AgreeBelow.mul
  · apply AgreeBelow.prod
    intro a ha
    exact ((hc _).shift _).mul (AgreeBelow.refl N _)
  · apply AgreeBelow.prod
    intro b hb
    exact hg _

lemma ratioSeries_mul_coeff_congr_loss (Y : ℝ) (F G : HierarchyJet) (p j s K : ℕ)
    {u v : Series}
    (hc : ∀q,AgreeBelow (K-(2*j+s)+1) (F.cusp q) (G.cusp q))
    (hg : ∀q,AgreeBelow (K-(2*j+s)+1) (F.genus q) (G.genus q))
    (hu : AgreeBelow (K-(2*j+s)+1) u v) :
    PowerSeries.coeff K (ratioSeries Y F p j s*u)=PowerSeries.coeff K (ratioSeries Y G p j s*v) := by
  rw [ratioSeries_mul_coeff,ratioSeries_mul_coeff]
  split_ifs
  · rw [((ratioCoreSeries_agree F G hc hg p j s).mul hu) _ (by omega)]
  · rfl

lemma ratioSeries_coeff_congr_loss (Y : ℝ) (F G : HierarchyJet) (p j s K : ℕ)
    (hc : ∀q,AgreeBelow (K-(2*j+s)+1) (F.cusp q) (G.cusp q))
    (hg : ∀q,AgreeBelow (K-(2*j+s)+1) (F.genus q) (G.genus q)) :
    PowerSeries.coeff K (ratioSeries Y F p j s)=PowerSeries.coeff K (ratioSeries Y G p j s) := by
  simpa only [mul_one] using ratioSeries_mul_coeff_congr_loss Y F G p j s K hc hg
    (AgreeBelow.refl _ (1:Series))

lemma mergerSeries_coeff_congr (Y : ℝ) (F G : HierarchyJet) (K t : ℕ) (d : List ℕ)
    (hp : ∀e,AgreeBelow K (F.profile e) (G.profile e))
    (hc : ∀p,AgreeBelow K (F.cusp p) (G.cusp p)) :
    PowerSeries.coeff K (mergerSeries Y F t d)=PowerSeries.coeff K (mergerSeries Y G t d) := by
  have hsum : AgreeBelow K
      (∑j∈Finset.range d.length,C (2*(d[j]!:ℝ)+1)*coefficientSum (fun l=>
        if 1≤t+d[j]!+l then C (weight Y l)*complexityShift 1 (F.profile ((t+d[j]!+l-1)::d.eraseIdx j)) else 0))
      (∑j∈Finset.range d.length,C (2*(d[j]!:ℝ)+1)*coefficientSum (fun l=>
        if 1≤t+d[j]!+l then C (weight Y l)*complexityShift 1 (G.profile ((t+d[j]!+l-1)::d.eraseIdx j)) else 0)) := by
    apply AgreeBelow.sum
    intro j hj
    apply (AgreeBelow.refl K _).mul
    apply AgreeBelow.coefficientSum
    intro l
    by_cases h : 1≤t+d[j]!+l
    · simp only [if_pos h]
      exact (AgreeBelow.refl K _).mul ((hp _).shift 1)
    · simp only [if_neg h]
      exact AgreeBelow.refl K _
  have hrest:=((hc d.length).shift 1).mul hsum
  have hzero : constantCoeff (C (A Y)*shiftVariable 1)=0 := by simp
  simpa only [mergerSeries,mul_assoc] using coeff_mul_eq_of_zero_constant hzero hrest

lemma nonseparatingSeries_coeff_congr (Y : ℝ) (F G : HierarchyJet) (K t : ℕ) (d : List ℕ)
    (hp : ∀e,AgreeBelow K (F.profile e) (G.profile e))
    (hc : ∀p,AgreeBelow K (F.cusp p) (G.cusp p))
    (hg : ∀p,AgreeBelow K (F.genus p) (G.genus p)) :
    PowerSeries.coeff K (nonseparatingSeries Y F t d)=PowerSeries.coeff K (nonseparatingSeries Y G t d) := by
  have hsum : AgreeBelow K (coefficientSum (fun l=>C (weight Y l)*
      ∑u∈Finset.range (t+l-1),complexityShift 1 (F.profile (u::(t+l-2-u)::d))))
      (coefficientSum (fun l=>C (weight Y l)*
      ∑u∈Finset.range (t+l-1),complexityShift 1 (G.profile (u::(t+l-2-u)::d)))) := by
    apply AgreeBelow.coefficientSum
    intro l
    apply (AgreeBelow.refl K _).mul
    apply AgreeBelow.sum
    intro u hu
    exact (hp _).shift 1
  have hrest:=(((hc (d.length+2)).shift 1).mul (hg (d.length+1))).mul hsum
  have hzero : constantCoeff (C (2*A Y)*shiftVariable 1)=0 := by simp
  simpa only [nonseparatingSeries,mul_assoc] using coeff_mul_eq_of_zero_constant hzero hrest
lemma separatingSeries_coeff_congr (P : PsiTheory) (Y : ℝ) (F G : HierarchyJet) (K t : ℕ) (d : List ℕ)
    (hp : ∀e,AgreeBelow K (F.profile e) (G.profile e))
    (hc : ∀p,AgreeBelow K (F.cusp p) (G.cusp p))
    (hg : ∀p,AgreeBelow K (F.genus p) (G.genus p)) :
    PowerSeries.coeff K (separatingSeries P Y F K t d)=PowerSeries.coeff K (separatingSeries P Y G K t d) := by
  unfold separatingSeries
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤K
  · rw [if_pos h,if_pos h]
    apply ratioSeries_mul_coeff_congr_loss
    · intro q
      exact (hc q).mono (by omega)
    · intro q
      exact (hg q).mono (by omega)
    · have hinner : AgreeBelow K
          (coefficientSum (fun l=>C (weight Y l)*∑u∈Finset.range (t+l-1),
            C (smallW P Y j (u::selectedNat d I))*complexityShift (2*j+I.card)
              (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))))
          (coefficientSum (fun l=>C (weight Y l)*∑u∈Finset.range (t+l-1),
            C (smallW P Y j (u::selectedNat d I))*complexityShift (2*j+I.card)
              (G.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))) := by
        apply AgreeBelow.coefficientSum
        intro l
        apply (AgreeBelow.refl K _).mul
        apply AgreeBelow.sum
        intro u hu
        exact (AgreeBelow.refl K _).mul ((hp _).shift _)
      exact hinner.mono (by omega)
  · rw [if_neg h,if_neg h]

lemma adjacentCoefficient_coeff_congr (P : PsiTheory) (Y : ℝ) (F G : HierarchyJet) (K i : ℕ) (d : List ℕ)
    (hp : ∀e,AgreeBelow K (F.profile e) (G.profile e))
    (hc : ∀p,AgreeBelow K (F.cusp p) (G.cusp p))
    (hg : ∀p,AgreeBelow K (F.genus p) (G.genus p)) :
    adjacentCoefficient P Y F K i d=adjacentCoefficient P Y G K i d := by
  unfold adjacentCoefficient
  simp only [map_add]
  rw [mergerSeries_coeff_congr Y F G K _ _ hp hc,
    nonseparatingSeries_coeff_congr Y F G K _ _ hp hc hg,
    separatingSeries_coeff_congr P Y F G K _ _ hp hc hg]

lemma profileAtOrder_coeff_congr (P : PsiTheory) (Y : ℝ) (F G : HierarchyJet) (K : ℕ) (d : List ℕ)
    (hp : ∀e,AgreeBelow K (F.profile e) (G.profile e))
    (hc : ∀p,AgreeBelow K (F.cusp p) (G.cusp p))
    (hg : ∀p,AgreeBelow K (F.genus p) (G.genus p)) :
    profileAtOrder P Y F K d=profileAtOrder P Y G K d := by
  unfold profileAtOrder
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro t ht
  exact adjacentCoefficient_coeff_congr P Y F G K i _ hp hc hg

def formalHierarchyJet (P : PsiTheory) (Y : ℝ) : HierarchyJet :=
  ⟨formalProfile P Y,formalCusp P Y,formalGenus P Y⟩

lemma profileCoefficient_succ_recursion (P : PsiTheory) (Y : ℝ) (d : List ℕ) (k : ℕ) :
    profileCoefficient P Y d (k+1)=profileAtOrder P Y (formalHierarchyJet P Y) (k+1) d := by
  change PowerSeries.coeff (k+1) (setCoeff ((hierarchyJet P Y k).profile d) (k+1)
    (profileAtOrder P Y (hierarchyJet P Y k) (k+1) d))=_
  rw [setCoeff_same]
  exact (profileAtOrder_coeff_congr P Y (formalHierarchyJet P Y) (hierarchyJet P Y k) (k+1) d
    (fun e=>formalProfile_stage_agree P Y e k) (fun p=>formalCusp_stage_agree P Y p k)
    (fun p=>formalGenus_stage_agree P Y p k)).symm

lemma formalProfile_coefficient_path_rule (P : PsiTheory) (Y : ℝ) (d : List ℕ) (k : ℕ) (hk : 0<k) :
    PowerSeries.coeff k (formalProfile P Y d)=profileAtOrder P Y (formalHierarchyJet P Y) k d := by
  cases k with
  | zero => omega
  | succ k => simpa only [formalProfile,PowerSeries.coeff_mk] using profileCoefficient_succ_recursion P Y d k
end WP.HigherOrder
