import WPFormalization.HigherOrder.FiniteRatioRecipe
import WPFormalization.HigherOrder.FiniteUnitInversion
import WPFormalization.HigherOrder.SmallThetaData
/-! The current genus coefficients have genuine finite kernel-data recipes.
The high-marking KdV step uses the already constructed current profile and
strictly lower scalar orders; bounded components are eliminated by their
actual finite theta polynomials. The p=1 descent supplies the current genus-2
input internally and uses the forced-unit inverse template. These are explicit
induction steps, not an assertion that the complete C.3 induction is supplied. -/
noncomputable section
namespace WP.HigherOrder.KernelFiniteData
open Set PowerSeries
variable {R : Type*} [CommRing R] [Algebra ℝ R] [Algebra ℚ R]

lemma smallW_encoded_scalar_recipe (P : PsiTheory) (K g : ℕ) (d : List ℕ)
    (hs : Stable g d.length) (hp : 1 ≤ d.length) (hK : complexity g d.length ≤ K)
    (φ : ℝ → R →ₐ[ℝ] ℝ) (κ : ThetaPolynomial ((3*K)/2+1) →+* R)
    (hκ : ∀Y∈Icc (0:ℝ) y₀,(φ Y).toRingHom.comp κ=
      MvPolynomial.eval (fun i : Fin ((3*K)/2+2)=>theta Y i.val)) :
    ∃a : R,∀Y∈Icc (0:ℝ) y₀,smallW P Y g d=(φ Y) a := by
  obtain ⟨F,hdeg,hF⟩ := smallW_polynomial_in_finite_theta_data P K g d hs hp hK
  refine ⟨κ F,?_⟩
  intro Y hY
  rw [hF Y hY,←hκ Y hY]
  rfl

lemma current_genus_high_scalar_recipe_step (P : PsiTheory) (K : ℕ) (hK : 1 ≤ K)
    (φ : ℝ → R →ₐ[ℝ] ℝ) (E : List ℕ → R)
    (hE : ∀Y∈Icc (0:ℝ) y₀,∀d : List ℕ,1 ≤ d.length →
      profileCoefficient P Y d K=(φ Y) (E d))
    (A : R) (hA : ∀Y∈Icc (0:ℝ) y₀,(φ Y) A=WP.A Y)
    (c g : ℕ → ℕ → R)
    (hc : ∀p≥1,∀i≤K,∀Y∈Icc (0:ℝ) y₀,cuspCoefficient P Y p i=(φ Y) (c p i))
    (hg : ∀p≥1,∀i<K,∀Y∈Icc (0:ℝ) y₀,genusCoefficient P Y p i=(φ Y) (g p i))
    (κ : ThetaPolynomial ((3*K)/2+1) →+* R)
    (hκ : ∀Y∈Icc (0:ℝ) y₀,(φ Y).toRingHom.comp κ=
      MvPolynomial.eval (fun i : Fin ((3*K)/2+2)=>theta Y i.val)) :
    ∃gK : ℕ → R,∀p≥2,∀Y∈Icc (0:ℝ) y₀,genusCoefficient P Y p K=(φ Y) (gK p) := by
  classical
  have hsmall : ∀j s : ℕ,Stable j (s+2) ∧ 1 ≤ 2*j+s ∧ 2*j+s ≤ K →
      ∃a : R,∀Y∈Icc (0:ℝ) y₀,smallW P Y j (List.replicate (s+2) 0)=(φ Y) a := by
    intro j s hel
    apply smallW_encoded_scalar_recipe P K j (List.replicate (s+2) 0)
      (by simpa only [List.length_replicate] using hel.1) (by simp) _ φ κ hκ
    simp only [List.length_replicate,complexity]
    omega
  choose Q hQ using hsmall
  let G : ℕ → R := fun p=>E (1::List.replicate (p-1) 0)-3*
    ∑j∈Finset.range (K+1),∑s∈Finset.range (p-1),
      if h : Stable j (s+2) ∧ 1 ≤ 2*j+s ∧ 2*j+s ≤ K then
        (Nat.choose (p-2) s:R)*Q j s h*ratioCoefficientRecipe A c g p j s K else 0
  refine ⟨G,?_⟩
  intro p hp Y hY
  have he : PowerSeries.coeff K (formalGenus P Y p)=genusCoefficient P Y p K := by simp [formalGenus]
  rw [←he,formalGenus_kdv_coefficient P Y p hp K]
  simp only [genusSeries,map_sub,PowerSeries.coeff_C_mul,map_sum]
  have hprof : PowerSeries.coeff K (formalProfile P Y (1::List.replicate (p-1) 0))=
      (φ Y) (E (1::List.replicate (p-1) 0)) := by
    simpa only [formalProfile,PowerSeries.coeff_mk] using hE Y hY (1::List.replicate (p-1) 0) (by simp)
  rw [hprof]
  simp only [G,map_sub,map_mul,map_ofNat,map_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hel : Stable j (s+2) ∧ 1 ≤ 2*j+s ∧ 2*j+s ≤ K
  · rw [ite_eq_left hel,dite_eq_left hel]
    rw [mul_assoc,PowerSeries.coeff_C_mul,PowerSeries.coeff_C_mul]
    simp only [map_mul,map_natCast]
    rw [hQ j s hel Y hY]
    have hr := ratioCoefficientRecipe_eval P Y A c g p j s K K (φ Y).toRingHom
      (by omega) (by have ht:=Finset.mem_range.mp hs;omega) hel.2.1 le_rfl (hA Y hY)
      (by intro q hq i hi;exact hc q hq i (by omega) Y hY)
      (by intro q hq i hi;exact hg q hq i hi Y hY)
    change PowerSeries.coeff K (ratioSeries Y ⟨formalProfile P Y,formalCusp P Y,formalGenus P Y⟩ p j s)=
      (φ Y) (ratioCoefficientRecipe A c g p j s K) at hr
    rw [hr]
    ring
  · rw [ite_eq_right hel,dite_eq_right hel,map_zero,map_zero]
lemma current_genus_one_scalar_recipe_step (P : PsiTheory) (K : ℕ)
    (φ : ℝ → R →ₐ[ℝ] ℝ) (c g : ℕ → ℕ → R) (G₂ : R)
    (hG₂ : ∀Y∈Icc (0:ℝ) y₀,genusCoefficient P Y 2 K=(φ Y) G₂)
    (hc : ∀p≥1,∀i≤K,∀Y∈Icc (0:ℝ) y₀,cuspCoefficient P Y p i=(φ Y) (c p i))
    (hg : ∀i<K,∀Y∈Icc (0:ℝ) y₀,genusCoefficient P Y 2 i=(φ Y) (g 2 i)) :
    ∃G₁ : R,∀Y∈Icc (0:ℝ) y₀,genusCoefficient P Y 1 K=(φ Y) G₁ := by
  classical
  let a : ℕ → R := fun i=>if i=K then G₂ else g 2 i
  let B : PowerSeries R := scalarShiftSeries (-1) a*PowerSeries.mk (c 3)*
    PowerSeries.mk (fun i=>unitInverseRecipe K i (c 1))
  refine ⟨PowerSeries.coeff K B,?_⟩
  intro Y hY
  have ha : ∀i≤K,PowerSeries.coeff i (formalGenus P Y 2)=(φ Y) (a i) := by
    intro i hi
    by_cases hiK : i=K
    · subst i
      simpa only [a,ite_true,formalGenus,PowerSeries.coeff_mk] using hG₂ Y hY
    · simpa only [a,ite_eq_right hiK,formalGenus,PowerSeries.coeff_mk] using hg i (by omega) Y hY
  have hs := scalarShiftSeries_map_agree (-1) a K (φ Y).toRingHom (formalGenus P Y 2) ha
  have hcus : AgreeBelow (K+1) (PowerSeries.map (φ Y).toRingHom (PowerSeries.mk (c 3)))
      (formalCusp P Y 3) := by
    intro i hi
    rw [PowerSeries.coeff_map,PowerSeries.coeff_mk]
    simpa only [formalCusp,PowerSeries.coeff_mk,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using (hc 3 (by omega) i (by omega) Y hY).symm
  have hinv : AgreeBelow (K+1)
      (PowerSeries.map (φ Y).toRingHom (PowerSeries.mk (fun i=>unitInverseRecipe K i (c 1))))
      (formalCusp P Y 1)⁻¹ := by
    intro i hi
    rw [PowerSeries.coeff_map,PowerSeries.coeff_mk]
    exact unitInverseRecipe_eval K i (by omega) (c 1) (φ Y) (formalCusp P Y 1)
      (formalCusp_constant P Y 1) (by
        intro k hk
        simpa only [formalCusp,PowerSeries.coeff_mk,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using (hc 1 (by omega) k hk Y hY).symm)
  have hm := (hs.mul hcus).mul hinv
  have hx : PowerSeries.coeff K (PowerSeries.map (φ Y).toRingHom B)=
      PowerSeries.coeff K (complexityShift (-1) (formalGenus P Y 2)*formalCusp P Y 3*(formalCusp P Y 1)⁻¹) := by
    simpa only [B,map_mul,Int.cast_neg,Int.cast_one] using hm K (by omega)
  have hd := congrArg (PowerSeries.coeff K) (formalGenus_descent P Y 1 (by omega))
  calc genusCoefficient P Y 1 K=PowerSeries.coeff K (formalGenus P Y 1) := by simp only [formalGenus,PowerSeries.coeff_mk]
       _ = PowerSeries.coeff K (complexityShift (-1) (formalGenus P Y 2)*formalCusp P Y 3*(formalCusp P Y 1)⁻¹) := by
          simpa only [descendGenus,Nat.reduceAdd] using hd
       _ = (φ Y) (PowerSeries.coeff K B) := by simpa only [PowerSeries.coeff_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hx.symm

lemma current_genus_scalar_recipe_step (P : PsiTheory) (K : ℕ) (hK : 1 ≤ K)
    (φ : ℝ → R →ₐ[ℝ] ℝ) (E : List ℕ → R)
    (hE : ∀Y∈Icc (0:ℝ) y₀,∀d : List ℕ,1 ≤ d.length →
      profileCoefficient P Y d K=(φ Y) (E d))
    (A : R) (hA : ∀Y∈Icc (0:ℝ) y₀,(φ Y) A=WP.A Y)
    (c g : ℕ → ℕ → R)
    (hc : ∀p≥1,∀i≤K,∀Y∈Icc (0:ℝ) y₀,cuspCoefficient P Y p i=(φ Y) (c p i))
    (hg : ∀p≥1,∀i<K,∀Y∈Icc (0:ℝ) y₀,genusCoefficient P Y p i=(φ Y) (g p i))
    (κ : ThetaPolynomial ((3*K)/2+1) →+* R)
    (hκ : ∀Y∈Icc (0:ℝ) y₀,(φ Y).toRingHom.comp κ=
      MvPolynomial.eval (fun i : Fin ((3*K)/2+2)=>theta Y i.val)) :
    ∃gK : ℕ → R,∀p≥1,∀Y∈Icc (0:ℝ) y₀,genusCoefficient P Y p K=(φ Y) (gK p) := by
  classical
  obtain ⟨G,hG⟩ := current_genus_high_scalar_recipe_step P K hK φ E hE A hA c g hc hg κ hκ
  obtain ⟨G₁,hG₁⟩ := current_genus_one_scalar_recipe_step P K φ c g (G 2) (hG 2 le_rfl) hc
    (fun i hi Y hY=>hg 2 (by omega) i hi Y hY)
  refine ⟨fun p=>if p=1 then G₁ else G p,?_⟩
  intro p hp Y hY
  by_cases hp1 : p=1
  · subst p
    simpa only [ite_true] using hG₁ Y hY
  · simpa only [ite_eq_right hp1] using hG p (by omega) Y hY

end WP.HigherOrder.KernelFiniteData
