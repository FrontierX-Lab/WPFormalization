import WPFormalization.Intersection.ComplexBackground
/-! The actual complex finite-background positive recursion is homogeneous in
its canonical theta factors. A strong induction on complexity bounds every
nonempty normalized amplitude by u^h times its true critical amplitude when
all theta coefficients have norm at most u. Finite signed children, invalid
states, top degree, and the h=1 genus-one base are handled explicitly.
The empty tuple is left to the genuine dilaton identity in the client. -/
set_option maxHeartbeats 800000
noncomputable section
open Set
open scoped Topology
namespace WP.Analysis
lemma complex_norm_add_le_scaled {x y : ℂ} {a b q : ℝ}
    (hx : ‖x‖≤q*a) (hy : ‖y‖≤q*b) : ‖x+y‖≤q*(a+b) := by
  exact (norm_add_le _ _).trans ((add_le_add hx hy).trans_eq (by ring))
lemma complex_norm_sum_le_scaled {ι : Type*} (s : Finset ι) (x : ι → ℂ) (a : ι → ℝ) (q : ℝ)
    (h : ∀ i∈s,‖x i‖≤q*a i) : ‖∑ i∈s,x i‖≤q*∑ i∈s,a i := by
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum h).trans_eq (Finset.mul_sum ..).symm)
lemma complex_norm_real_mul_le_scaled {x : ℂ} {a q c : ℝ} (hc : 0≤c)
    (hx : ‖x‖≤q*a) : ‖(c:ℂ)*x‖≤q*(c*a) := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left hx hc).trans_eq (by ring)
lemma complex_norm_mul_le_scaled {x y : ℂ} {a b q r : ℝ}
    (hx : ‖x‖≤q*a) (hy : ‖y‖≤r*b) (hq : 0≤q) (ha : 0≤a) : ‖x*y‖≤(q*r)*(a*b) := by
  rw [norm_mul]
  exact (mul_le_mul hx hy (norm_nonneg _) (mul_nonneg hq ha)).trans_eq (by ring)

lemma normalizedChildren_piSigned_formula (P : PsiTheory) (g p : ℕ) (d : List ℤ) (Y : ℝ) :
    normalizedChildren P g p d Y=
      (∑ j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*piSigned P g (((p:ℤ)+d[j]!-1)::d.eraseIdx j) Y)+
      (if g=0 then 0 else (1/2:ℝ)*∑ u∈Finset.range (p-1),piSigned P (g-1) ((u:ℤ)::((p:ℤ)-2-u)::d) Y)+
      (1/2:ℝ)*∑ u∈Finset.range (p-1),∑ g₁∈Finset.range (g+1),∑ I∈(Finset.range d.length).powerset,
        piSigned P g₁ ((u:ℤ)::selected d I) Y*
          piSigned P (g-g₁) (((p:ℤ)-2-u)::selected d ((Finset.range d.length)\I)) Y := rfl

lemma complexNormalizedChildren_homogeneous_step (P : PsiTheory) (R : ℂ → ℂ) (g p h : ℕ) (d : List ℤ)
    (z : ℂ) (u : ℝ) (hu : 1≤u) (hh : 2≤h) (he : complexity g (d.length+1)=h)
    (hd : ∀ k∈d,0≤k)
    (ih : ∀ g' : ℕ,∀ c : List ℤ,1≤c.length → complexity g' c.length<h →
      ‖complexPiSigned P R g' c z‖≤u^(complexity g' c.length)*piSigned P g' c y₀) :
    ‖complexNormalizedChildren P R g p d z‖≤u^(h-1)*normalizedChildren P g p d y₀ := by
  have hu0 : 0≤u := by linarith
  have hhalf : (1/2:ℂ)=((1/2:ℝ):ℂ) := by norm_num
  rw [normalizedChildren_piSigned_formula]
  unfold complexNormalizedChildren
  apply complex_norm_add_le_scaled
  · apply complex_norm_add_le_scaled
    · apply complex_norm_sum_le_scaled
      intro j hj
      have hj' := Finset.mem_range.mp hj
      let c := ((p:ℤ)+d[j]!-1)::d.eraseIdx j
      have hc : complexity g c.length=h-1 := by
        dsimp only [c]
        simp only [List.length_cons,List.length_eraseIdx_of_lt hj']
        unfold complexity at *
        omega
      have hi := ih g c (by simp [c]) (by omega)
      rw [hc] at hi
      have hcoef : 0≤2*(d[j]!:ℝ)+1 := by
        have hmem : d[j]!∈d := by simpa [hj'] using (List.getElem_mem (l:=d) hj')
        have hk := hd (d[j]!) hmem
        have hk' : (0:ℝ)≤(d[j]!:ℝ) := by exact_mod_cast hk
        linarith
      have hcast : (2*(d[j]!:ℂ)+1)=(((2*(d[j]!:ℝ)+1):ℝ):ℂ) := by push_cast;rfl
      rw [hcast]
      exact complex_norm_real_mul_le_scaled hcoef hi
    · by_cases hg : g=0
      · simp only [ite_eq_left hg,norm_zero,mul_zero]
        exact le_rfl
      · simp only [ite_eq_right hg]
        rw [hhalf]
        apply complex_norm_real_mul_le_scaled (by norm_num : (0:ℝ)≤1/2)
        apply complex_norm_sum_le_scaled
        intro v hv
        let c := (v:ℤ)::((p:ℤ)-2-v)::d
        have hc : complexity (g-1) c.length=h-1 := by
          dsimp only [c]
          simp only [List.length_cons]
          unfold complexity at *
          omega
        simpa only [hc] using ih (g-1) c (by simp [c]) (by omega)
  · rw [hhalf]
    apply complex_norm_real_mul_le_scaled (by norm_num : (0:ℝ)≤1/2)
    apply complex_norm_sum_le_scaled
    intro v hv
    apply complex_norm_sum_le_scaled
    intro g₁ hg₁
    apply complex_norm_sum_le_scaled
    intro I hI
    let c₁ : List ℤ := (v:ℤ)::selected d I
    let c₂ : List ℤ := ((p:ℤ)-2-v)::selected d ((Finset.range d.length)\I)
    change ‖complexPiSigned P R g₁ c₁ z*complexPiSigned P R (g-g₁) c₂ z‖≤
      u^(h-1)*(piSigned P g₁ c₁ y₀*piSigned P (g-g₁) c₂ y₀)
    by_cases hs₁ : Stable g₁ c₁.length
    · by_cases hs₂ : Stable (g-g₁) c₂.length
      · have hgg : g₁≤g := by have := Finset.mem_range.mp hg₁;omega
        have hpart := selected_partition_length d I
        have hc₁ : complexity g₁ c₁.length<h := by
          dsimp only [c₁,c₂] at hs₁ hs₂ ⊢
          simp only [Stable,List.length_cons] at hs₁ hs₂ ⊢
          unfold complexity at *
          omega
        have hc₂ : complexity (g-g₁) c₂.length<h := by
          dsimp only [c₁,c₂] at hs₁ hs₂ ⊢
          simp only [Stable,List.length_cons] at hs₁ hs₂ ⊢
          unfold complexity at *
          omega
        have hcs : complexity g₁ c₁.length+complexity (g-g₁) c₂.length=h-1 := by
          dsimp only [c₁,c₂] at hs₁ hs₂ ⊢
          simp only [Stable,List.length_cons] at hs₁ hs₂ ⊢
          unfold complexity at *
          omega
        have hi₁ := ih g₁ c₁ (by simp [c₁]) hc₁
        have hi₂ := ih (g-g₁) c₂ (by simp [c₂]) hc₂
        have hp := complex_norm_mul_le_scaled hi₁ hi₂ (pow_nonneg hu0 _) (piSigned_critical_nonneg P g₁ c₁)
        rw [←pow_add,hcs] at hp
        exact hp
      · rw [complexPiSigned_unstable P R _ _ hs₂,piSigned_unstable P _ _ y₀ hs₂]
        simp
    · rw [complexPiSigned_unstable P R _ _ hs₁,piSigned_unstable P _ _ y₀ hs₁]
      simp
end WP.Analysis
namespace WP.Analysis
lemma complexNormalized_homogeneous_upper_aux (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (z : ℂ) (hz : z∈Ω) (u : ℝ) (hu : 1≤u) (hθ : ∀ l,‖complexThetaCoeff R l z‖≤u) (h : ℕ) :
    ∀ g : ℕ,∀ d : List ℕ,1≤d.length → complexity g d.length=h →
      ‖complexNormalized P R g d z‖≤u^h*normalized P g d y₀ := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro g d hn he
    have hu0 : 0≤u := by linarith
    by_cases hs : Stable g d.length
    · by_cases hd : d.sum≤dimension g d.length
      · by_cases htop : d.sum=dimension g d.length
        · rw [complexNormalized_top Ω hconn hcover P R hK hKr g d htop z hz]
          simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (normalized_critical_nonneg P g d)]
          apply le_mul_of_one_le_left (normalized_critical_nonneg P g d)
          have hp := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) hu h
          simpa only [one_pow] using hp
        · by_cases hsmall : h≤1
          · have hg : g=1 := by
              unfold complexity at he
              unfold Stable at hs
              unfold dimension at hd htop
              omega
            have hlen : d.length=1 := by unfold complexity at he;unfold Stable at hs;omega
            subst g
            obtain ⟨p,rfl⟩ := List.length_eq_one_iff.mp hlen
            have hp : p=0 := by
              simp only [List.sum_singleton,List.length_singleton] at hd htop
              norm_num [dimension] at hd htop
              omega
            subst p
            have hh1 : h=1 := by norm_num [complexity] at he;omega
            rw [complexNormalized_one_zero Ω hconn hcover P R hK hKr z hz,
              (initial_amplitudes P y₀ ⟨y₀_pos.le,le_rfl⟩).2.2,critical_kernels.2 1,hh1,pow_one,norm_div]
            have ht := hθ 1
            norm_num
            nlinarith
          · have hh : 2≤h := by omega
            cases d with
            | nil => simp at hn
            | cons p d =>
              have hhc : 2≤complexity g (d.length+1) := by simpa only [List.length_cons] using he.symm ▸ hh
              rw [complexNormalized_positive_convolution Ω hconn hcover P R hK hKr g p d hhc hd z hz,
                normalized_positive_convolution P g p d y₀ hhc hd ⟨y₀_pos.le,le_rfl⟩]
              simp only [critical_kernels.2,one_mul]
              apply complex_norm_sum_le_scaled
              intro l hl
              have hchild := complexNormalizedChildren_homogeneous_step P R g (p+l) h (d.map Int.ofNat) z u hu hh
                (by simpa only [List.length_map,List.length_cons] using he)
                (by intro k hk;obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hk;exact Int.natCast_nonneg j)
                (by
                  intro g' c hlen hc
                  unfold complexPiSigned piSigned
                  split_ifs
                  · simpa only [List.length_map] using ih _ hc g' (c.map Int.toNat)
                      (by simpa only [List.length_map] using hlen) (by simp only [List.length_map])
                  · simp)
              rw [norm_mul]
              have hb := mul_le_mul (hθ l) hchild (norm_nonneg _) hu0
              have hp : u*u^(h-1)=u^h := by rw [mul_comm,←pow_succ,Nat.sub_add_cancel (by omega : 1≤h)]
              exact hb.trans_eq (by rw [←mul_assoc,hp])
      · have hex : dimension g d.length<d.sum := by omega
        rw [complexNormalized_excess P R g d hex,normalized_excess P g d y₀ hex]
        simp
    · rw [complexNormalized_unstable P R g d hs,normalized_unstable P g d y₀ hs]
      simp

lemma complexNormalized_homogeneous_upper (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (z : ℂ) (hz : z∈Ω) (u : ℝ) (hu : 1≤u) (hθ : ∀ l,‖complexThetaCoeff R l z‖≤u)
    (g : ℕ) (d : List ℕ) (hn : 1≤d.length) :
    ‖complexNormalized P R g d z‖≤u^(complexity g d.length)*normalized P g d y₀ :=
  complexNormalized_homogeneous_upper_aux Ω hconn hcover P R hK hKr z hz u hu hθ _ g d hn rfl
end WP.Analysis
