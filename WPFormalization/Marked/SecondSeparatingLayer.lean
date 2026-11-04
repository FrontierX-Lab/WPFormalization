import WPFormalization.Marked.SecondSeparatingLeading

/-! The complete signed separating recursion layer has the explicit Appendix C.1 leading term and a uniform cubic remainder. -/

noncomputable section
open Set

namespace WP

def secondSeparatingLayer (P : PsiTheory) (g k : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  (1/2:ℝ)*∑ u∈Finset.range (k-1),∑ j∈Finset.range (g+1),∑ I∈(Finset.range d.length).powerset,
    secondSeparatingTerm P g k d u j I Y

lemma secondSeparatingLayer_as_normalized (P : PsiTheory) (g k : ℕ) (d : List ℕ) (Y : ℝ) :
    secondSeparatingLayer P g k d Y=
      (1/2:ℝ)*(4:ℝ)^g*
        (∑ u∈Finset.range (k-1),∑ j∈Finset.range (g+1),∑ I∈(Finset.range d.length).powerset,
          normInt P j ((u:ℤ)::selected (d.map Int.ofNat) I) Y*
          normInt P (g-j) (((k:ℤ)-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I)) Y)/
            W P g (d.length+1) Y := by
  unfold secondSeparatingLayer secondSeparatingTerm
  simp only [Finset.sum_div,Finset.mul_sum,mul_assoc,mul_div_assoc]

lemma secondSeparatingLayer_decomposition (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (hg : 3 ≤ g) (Y : ℝ) :
    secondSeparatingLayer P g k d Y=secondSeparatingSphere P g k d Y+
      secondSeparatingTorus P g k d Y+secondSeparatingRemainder P g k d Y/2 := by
  rw [secondSeparatingLayer,secondSeparating_decomposition P g k d hg Y,
    secondSeparatingLeading_sphere_torus P g k d (by omega) Y]
  ring

lemma secondSeparatingLayer_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ k : ℕ,∀ d : List ℕ,d.length+1=p →
      ∀ Y∈Icc (0:ℝ) y₀,
      |secondSeparatingLayer P g k d Y-
        (A Y)^2/(complexity g p:ℝ)^2*
          ((if 2 ≤ k then (Nat.choose (zeros d) 2:ℝ)+theta Y 1/2 else 0)+
            (if 3 ≤ k then (1/2:ℝ) else 0))| ≤
        C*((k+d.sum:ℕ)+1:ℝ)^2/(complexity g p:ℝ)^3 := by
  obtain ⟨Cs,hCs,Gs,hS⟩ := secondSeparatingSphere_uniform P p hp
  obtain ⟨Ct,hCt,Gt,hT⟩ := secondSeparatingTorus_uniform P p hp
  obtain ⟨Cr,hCr,Gr,hR⟩ := secondSeparatingRemainder_uniform P p hp
  refine ⟨Cs+Ct+Cr/2,by positivity,max 3 (max Gs (max Gt Gr)),?_⟩
  intro g hg k d hd Y hY
  have hg3 : 3 ≤ g := (le_max_left _ _).trans hg
  have hgS : Gs ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgT : Gt ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hg))
  have hgR : Gr ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hg))
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  let L : ℝ := ((k+d.sum:ℕ)+1:ℝ)
  have hpoly : (k:ℝ)+1 ≤ L^2 := by
    dsimp [L]
    simp only [Nat.cast_add]
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
    have hd' : (0:ℝ) ≤ d.sum := Nat.cast_nonneg _
    nlinarith [sq_nonneg ((k:ℝ)+d.sum)]
  have hr := hR g hgR k d hd Y hY
  have hr' : |secondSeparatingRemainder P g k d Y/2| ≤ (Cr/2)*L^2/(complexity g p:ℝ)^3 := by
    rw [abs_of_nonneg (div_nonneg hr.1 (by norm_num))]
    calc
      _ ≤ (Cr*((k:ℝ)+1)/(complexity g p:ℝ)^3)/2 := div_le_div_of_nonneg_right hr.2 (by norm_num)
      _ ≤ (Cr*L^2/(complexity g p:ℝ)^3)/2 := by gcongr
      _ = _ := by ring
  let S₀ : ℝ := if 2 ≤ k then (Nat.choose (zeros d) 2:ℝ)*(A Y)^2/(complexity g p:ℝ)^2 else 0
  let T₀ : ℝ := ((if 2 ≤ k then theta Y 1/2 else 0)+(if 3 ≤ k then (1/2:ℝ) else 0))*
    (A Y)^2/(complexity g p:ℝ)^2
  have hcenter : (A Y)^2/(complexity g p:ℝ)^2*
      ((if 2 ≤ k then (Nat.choose (zeros d) 2:ℝ)+theta Y 1/2 else 0)+
        (if 3 ≤ k then (1/2:ℝ) else 0))=S₀+T₀ := by
    dsimp [S₀,T₀]
    split_ifs <;> ring
  rw [hcenter,secondSeparatingLayer_decomposition P g k d hg3 Y]
  have he : secondSeparatingSphere P g k d Y+secondSeparatingTorus P g k d Y+
      secondSeparatingRemainder P g k d Y/2-(S₀+T₀)=
      (secondSeparatingSphere P g k d Y-S₀)+(secondSeparatingTorus P g k d Y-T₀)+
        secondSeparatingRemainder P g k d Y/2 := by ring
  rw [he]
  calc
    _ ≤ |secondSeparatingSphere P g k d Y-S₀|+|secondSeparatingTorus P g k d Y-T₀|+
        |secondSeparatingRemainder P g k d Y/2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ Cs*L^2/(complexity g p:ℝ)^3+Ct*L^2/(complexity g p:ℝ)^3+(Cr/2)*L^2/(complexity g p:ℝ)^3 :=
      add_le_add (add_le_add (hS g hgS k d hd Y hY) (hT g hgT k d hd Y hY)) hr'
    _ = _ := by dsimp [L];ring
end WP
