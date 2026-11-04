import WPFormalization.HigherOrder.TriangularLocality

/-! The actual canonical finite hierarchy satisfies its coefficient rules and is their unique solution. All these existence and uniqueness statements are proved; the rule predicate is not an external interface. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma hierarchy_unique_of_coefficient_rules (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀)
    (F : HierarchyJet)
    (hp0 : ∀d,constantCoeff (F.profile d)=1)
    (hc0 : ∀p,constantCoeff (F.cusp p)=1)
    (hg0 : ∀p,constantCoeff (F.genus p)=1)
    (hprofile : ∀k:ℕ,0<k→∀d:List ℕ,PowerSeries.coeff k (F.profile d)=profileAtOrder P Y F k d)
    (hcusp : ∀p:ℕ,F.cusp p=cuspSeries Y F.profile p)
    (hgenus : ∀p:ℕ,2≤p→∀k:ℕ,PowerSeries.coeff k (F.genus p)=
      PowerSeries.coeff k (genusSeries P Y F F.profile k p))
    (hdescent : ∀p:ℕ,p≤1→F.genus p=descendGenus F.cusp (F.genus (p+1)) p) :
    F=formalHierarchyJet P Y := by
  let G:=formalHierarchyJet P Y
  have hall (K:ℕ) : (∀d:List ℕ,PowerSeries.coeff K (F.profile d)=PowerSeries.coeff K (G.profile d)) ∧
      (∀p:ℕ,PowerSeries.coeff K (F.cusp p)=PowerSeries.coeff K (G.cusp p)) ∧
      (∀p:ℕ,PowerSeries.coeff K (F.genus p)=PowerSeries.coeff K (G.genus p)) := by
    induction K using Nat.strong_induction_on with
    | h K ih =>
      by_cases hK : K=0
      · subst K
        simp [coeff_zero_eq_constantCoeff,G,formalHierarchyJet,hp0,hc0,hg0]
      · have hp : ∀d,AgreeBelow K (F.profile d) (G.profile d) := fun d k hk=>(ih k hk).1 d
        have hc : ∀p,AgreeBelow K (F.cusp p) (G.cusp p) := fun p k hk=>(ih k hk).2.1 p
        have hg : ∀p,AgreeBelow K (F.genus p) (G.genus p) := fun p k hk=>(ih k hk).2.2 p
        have hpK (d:List ℕ) : PowerSeries.coeff K (F.profile d)=PowerSeries.coeff K (G.profile d) := by
          rw [hprofile K (by omega)]
          change _=PowerSeries.coeff K (formalProfile P Y d)
          rw [formalProfile_coefficient_path_rule P Y d K (by omega)]
          exact profileAtOrder_coeff_congr P Y F G K d hp hc hg
        have hpFull : ∀d,AgreeBelow (K+1) (F.profile d) (G.profile d) := by
          intro d k hk
          by_cases he : k=K
          · subst k;exact hpK d
          · exact hp d k (by omega)
        have hcK (p:ℕ) : PowerSeries.coeff K (F.cusp p)=PowerSeries.coeff K (G.cusp p) := by
          rw [hcusp p]
          change _=PowerSeries.coeff K (formalCusp P Y p)
          rw [formalCusp_recursion P Y hY p]
          exact (cuspSeries_agree Y p hpFull) K (by omega)
        have hcFull : ∀p,AgreeBelow (K+1) (F.cusp p) (G.cusp p) := by
          intro p k hk
          by_cases he : k=K
          · subst k;exact hcK p
          · exact hc p k (by omega)
        have hgKhigh (p:ℕ) (hp2:2≤p) : PowerSeries.coeff K (F.genus p)=PowerSeries.coeff K (G.genus p) := by
          rw [hgenus p hp2 K]
          change _=PowerSeries.coeff K (formalGenus P Y p)
          rw [formalGenus_kdv_coefficient P Y p hp2 K]
          exact genusSeries_coeff_congr P Y F G F.profile G.profile K p hpFull hc hg
        have hgFull2 : AgreeBelow (K+1) (F.genus 2) (G.genus 2) := by
          intro k hk
          by_cases he : k=K
          · subst k;exact hgKhigh 2 (by omega)
          · exact hg 2 k (by omega)
        have hgK1 : PowerSeries.coeff K (F.genus 1)=PowerSeries.coeff K (G.genus 1) := by
          rw [hdescent 1 (by omega)]
          change _=PowerSeries.coeff K (formalGenus P Y 1)
          rw [formalGenus_descent P Y 1 (by omega)]
          exact (descendGenus_agree hcFull hgFull2 1) K (by omega)
        have hgFull1 : AgreeBelow (K+1) (F.genus 1) (G.genus 1) := by
          intro k hk
          by_cases he : k=K
          · subst k;exact hgK1
          · exact hg 1 k (by omega)
        have hgK0 : PowerSeries.coeff K (F.genus 0)=PowerSeries.coeff K (G.genus 0) := by
          rw [hdescent 0 (by omega)]
          change _=PowerSeries.coeff K (formalGenus P Y 0)
          rw [formalGenus_descent P Y 0 (by omega)]
          exact (descendGenus_agree hcFull hgFull1 0) K (by omega)
        refine ⟨hpK,hcK,?_⟩
        intro p
        rcases p with _|_|p
        · exact hgK0
        · exact hgK1
        · exact hgKhigh (p+2) (by omega)
  have hpEq : F.profile=G.profile := by
    funext d
    apply PowerSeries.ext
    intro k
    exact (hall k).1 d
  have hcEq : F.cusp=G.cusp := by
    funext p
    apply PowerSeries.ext
    intro k
    exact (hall k).2.1 p
  have hgEq : F.genus=G.genus := by
    funext p
    apply PowerSeries.ext
    intro k
    exact (hall k).2.2 p
  change HierarchyJet.mk F.profile F.cusp F.genus=HierarchyJet.mk G.profile G.cusp G.genus
  rw [hpEq,hcEq,hgEq]
def CanonicalHierarchyRules (P : PsiTheory) (Y : ℝ) (F : HierarchyJet) : Prop :=
  (∀d,constantCoeff (F.profile d)=1) ∧ (∀p,constantCoeff (F.cusp p)=1) ∧
  (∀p,constantCoeff (F.genus p)=1) ∧
  (∀k:ℕ,0<k→∀d:List ℕ,PowerSeries.coeff k (F.profile d)=profileAtOrder P Y F k d) ∧
  (∀p:ℕ,F.cusp p=cuspSeries Y F.profile p) ∧
  (∀p:ℕ,2≤p→∀k:ℕ,PowerSeries.coeff k (F.genus p)=PowerSeries.coeff k (genusSeries P Y F F.profile k p)) ∧
  (∀p:ℕ,p≤1→F.genus p=descendGenus F.cusp (F.genus (p+1)) p)

lemma formalHierarchyJet_rules (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    CanonicalHierarchyRules P Y (formalHierarchyJet P Y) := by
  refine ⟨fun d=>formalProfile_constant P Y d,fun p=>formalCusp_constant P Y p,
    fun p=>formalGenus_constant P Y p,?_,?_,?_,?_⟩
  · intro k hk d
    exact formalProfile_coefficient_path_rule P Y d k hk
  · intro p
    exact formalCusp_recursion P Y hY p
  · intro p hp k
    exact formalGenus_kdv_coefficient P Y p hp k
  · intro p hp
    exact formalGenus_descent P Y p hp

lemma canonicalHierarchy_existsUnique (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) :
    ∃! F:HierarchyJet,CanonicalHierarchyRules P Y F := by
  refine ⟨formalHierarchyJet P Y,formalHierarchyJet_rules P Y hY,?_⟩
  intro F hF
  exact hierarchy_unique_of_coefficient_rules P Y hY F hF.1 hF.2.1 hF.2.2.1
    hF.2.2.2.1 hF.2.2.2.2.1 hF.2.2.2.2.2.1 hF.2.2.2.2.2.2
end WP.HigherOrder
