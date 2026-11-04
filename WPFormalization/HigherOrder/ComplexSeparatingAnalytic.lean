import WPFormalization.HigherOrder.ComplexOperatorAnalytic
/-! Normal convergence of the actual separating kernel and its finite-loss
operator. Only earlier profile/scalar coefficients are used. The displayed
bounds are induction data, not added premises of a final paper theorem. -/
set_option maxHeartbeats 800000
noncomputable section
open Set PowerSeries
namespace WP.HigherOrder.ComplexCanonical
lemma separating_shifted_profile_norm_polynomial (M : ℝ) (hM1 : 1≤M) (K : ℕ)
    (F : HierarchyJet) (e : WP.HigherOrder.Series) (he : ∀n:ℕ,0≤PowerSeries.coeff n e)
    (hprofile : ∀i:ℕ,i≤K-1→∀d:List ℕ,1≤d.length→‖PowerSeries.coeff i (F.profile d)‖≤
      (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)
    (P : PsiTheory) (R : ℂ → ℂ) (z : ℂ) (j t : ℕ) (d : List ℕ) (I : Finset ℕ)
    (hr : 2≤2*j+I.card) (hrK : 2*j+I.card≤K) (B : ℝ) (hB : 0≤B)
    (hsmall : ∀u:ℕ,‖smallW P R z j (u::selectedNat d I)‖≤B)
    (n : ℕ) (hn : n+(2*j+I.card)≤K) (l : ℕ) :
    ‖PowerSeries.coeff n (∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z j (u::selectedNat d I))*
      complexityShift ((2*j+I.card:ℕ):ℂ)
        (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))‖≤
      (B*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e))*
        (profileOrderWeight M K (t::d)+l+1)^(2*n+1) := by
  have hM0:0≤M:=by linarith
  let r:=2*j+I.card
  let S:=profileOrderWeight M K (t::d)
  have hKS:(K:ℝ)≤S:=by
    have hm:=mul_le_mul_of_nonneg_right hM1 (Nat.cast_nonneg K : (0:ℝ)≤K)
    dsimp[S,profileOrderWeight]
    linarith [Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) (t::d).length]
  have hEN:=coeff_mul_nonneg exp_coeff_nonneg he
  let L:ℕ→Series:=fun l=>∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z j (u::selectedNat d I))*
    complexityShift r (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))
  have hL (l:ℕ) : ‖PowerSeries.coeff n (L l)‖≤
      (B*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e))*(S+l+1)^(2*n+1):=by
    have hSl:(K:ℝ)≤S+l+1:=by linarith[Nat.cast_nonneg (α:=ℝ) l]
    have hSl0:0≤S+l+1:=(Nat.cast_nonneg K).trans hSl
    have hpoint (u:ℕ) (hu:u∈Finset.range (t+l-1)) :
        ‖PowerSeries.coeff n (PowerSeries.C (smallW P R z j (u::selectedNat d I))*
          complexityShift r (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))‖≤
        B*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)):=by
      have hnorm:‖(r:ℂ)‖≤(K:ℝ):=by rw[Complex.norm_natCast];exact_mod_cast hrK
      have hshift:=complex_shift_coeff_exponential_majorant (r:ℂ) (S+l+1)
        (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))
        (fun i=>PowerSeries.coeff i e) n K (by omega) hnorm hSl he (by
          intro i hi
          have hp:=hprofile i (by omega) ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)) (by simp)
          have hw:=separating_order_weight M hM0 i K t l u d ((Finset.range d.length)\I)
            (by omega) (Finset.mem_range.mp hu)
          have hw0:0≤profileOrderWeight M i ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)):=by
            unfold profileOrderWeight;positivity
          have hw':profileOrderWeight M i ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))≤S+l+1:=by
            dsimp[S];linarith
          simpa only[mul_comm] using hp.trans
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw' _) (he i)))
      have hmk:PowerSeries.mk (fun i=>PowerSeries.coeff i e)=e:=by ext i;simp
      rw[hmk] at hshift
      rw[PowerSeries.coeff_C_mul,norm_mul]
      exact mul_le_mul (hsmall u) (by simpa only[complexityShift,shiftVariable] using hshift)
        (norm_nonneg _) hB
    simp only[L,map_sum]
    apply (norm_sum_le _ _).trans
    calc
      _≤∑u∈Finset.range (t+l-1),B*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)):=
        Finset.sum_le_sum hpoint
      _=((t+l-1:ℕ):ℝ)*(B*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e))):=by
        simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      _≤(S+l+1)*(B*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e))):=
        mul_le_mul_of_nonneg_right
          ((pair_count_le_order_weight M hM0 K t l d).trans (by dsimp[S];linarith))
          (mul_nonneg hB (mul_nonneg (pow_nonneg hSl0 _) (hEN n)))
      _=_:=by rw[pow_succ];ring
  exact hL l


lemma separating_kernel_analyticCoefficients (Ω : Set ℂ) (hΩ : IsOpen Ω) (P : PsiTheory)
    (R : ℂ → ℂ) (ρ C : ℝ) (hρ : 1<ρ) (hC : 0≤C)
    (hwa : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexWeightCoeff R l) Ω)
    (hwg : ∀ l z,z∈Ω → ‖WP.Analysis.complexWeightCoeff R l z‖≤C/ρ^l)
    (M : ℝ) (hM1 : 1≤M) (K : ℕ) (F : ℂ → HierarchyJet) (e : WP.HigherOrder.Series)
    (he : ∀ n,0≤PowerSeries.coeff n e)
    (hprofile : ∀ z∈Ω,∀ i≤K-1,∀ d : List ℕ,1≤d.length →
      ‖PowerSeries.coeff i ((F z).profile d)‖≤(profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)
    (hpa : ∀ d : List ℕ,1≤d.length → AnalyticCoefficients Ω (K-1) (fun z=>(F z).profile d))
    (g t : ℕ) (d : List ℕ) (I : Finset ℕ) (hr : 2≤2*g+I.card) (hrK : 2*g+I.card≤K)
    (B : ℝ) (hB : 0≤B)
    (hsmall : ∀ z∈Ω,∀u,‖smallW P R z g (u::selectedNat d I)‖≤B)
    (hsmalla : ∀u,AnalyticOnNhd ℂ (fun z=>smallW P R z g (u::selectedNat d I)) Ω) :
    AnalyticCoefficients Ω (K-(2*g+I.card)) (fun z=>coefficientSum (fun l=>
      PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
        ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z g (u::selectedNat d I))*
          complexityShift ((2*g+I.card:ℕ):ℂ)
            ((F z).profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))) := by
  let L : ℕ → ℂ → Series := fun l z=>∑u∈Finset.range (t+l-1),
    PowerSeries.C (smallW P R z g (u::selectedNat d I))*
      complexityShift ((2*g+I.card:ℕ):ℂ)
        ((F z).profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))
  have hLa : ∀l,AnalyticCoefficients Ω (K-(2*g+I.card)) (L l) := by
    intro l
    apply AnalyticCoefficients.sum
    intro u hu
    apply (AnalyticCoefficients.C (hsmalla u)).mul
    exact ((hpa _ (by simp)).mono (by omega)).shift _
  have hLb : ∀n≤K-(2*g+I.card),∃ (D S : ℝ) (q : ℕ),0≤D ∧ 0≤S ∧
      ∀ l z,z∈Ω → ‖PowerSeries.coeff n (L l z)‖≤D*(S+l+1)^q := by
    intro n hn
    refine ⟨B*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e),profileOrderWeight M K (t::d),2*n+1,
      mul_nonneg hB (coeff_mul_nonneg exp_coeff_nonneg he n),?_,?_⟩
    · have hM0 : 0≤M := by linarith
      unfold profileOrderWeight
      positivity
    · intro l z hz
      exact separating_shifted_profile_norm_polynomial M hM1 K (F z) e he (hprofile z hz)
        P R z g t d I hr hrK B hB (hsmall z hz) n (by omega) l
  exact (AnalyticCoefficients.geometric_weighted_coefficientSum hΩ ρ C hρ hC
    (WP.Analysis.complexWeightCoeff R) hwa hwg L hLa hLb).2

lemma selected_smallW_uniform_bound (Ω : Set ℂ) (P : PsiTheory) (R : ℂ → ℂ)
    (T : ℝ) (hT : 1≤T)
    (hsmall : ∀g:ℕ,∀d:List ℕ,Stable g d.length → ∀z∈Ω,
      ‖WP.Analysis.complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length))
    (g : ℕ) (d : List ℕ) (I : Finset ℕ) (hI : I⊆Finset.range d.length) (hs : Stable g (I.card+1)) :
    ∃B:ℝ,0≤B ∧ ∀z∈Ω,∀u,‖smallW P R z g (u::selectedNat d I)‖≤B := by
  have hlen : (selectedNat d I).length=I.card := by
    rw [←selectedNat_toNat d I,List.length_map]
    exact selected_length_card (d.map Int.ofNat) I (by simpa only [List.length_map] using hI)
  let h := complexity g (I.card+1)
  have hh : 0<h := by dsimp [h,complexity];unfold Stable at hs;omega
  refine ⟨Real.Gamma (h:ℝ)*T^h,mul_nonneg
    (Real.Gamma_pos_of_pos (by exact_mod_cast hh)).le (pow_nonneg (by linarith) _),?_⟩
  intro z hz u
  have hu : (u::selectedNat d I).length=I.card+1 := by simp only [List.length_cons,hlen]
  simpa only [smallW,hu,h] using hsmall g (u::selectedNat d I) (by rw [hu];exact hs) z hz

lemma separatingSeries_analyticCoefficients (Ω : Set ℂ) (hΩ : IsOpen Ω) (P : PsiTheory)
    (R : ℂ → ℂ) (ρ C : ℝ) (hρ : 1<ρ) (hC : 0≤C)
    (hwa : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexWeightCoeff R l) Ω)
    (hwg : ∀ l z,z∈Ω → ‖WP.Analysis.complexWeightCoeff R l z‖≤C/ρ^l)
    (hA : AnalyticOnNhd ℂ (kernelA R) Ω)
    (hsa : ∀ g d,AnalyticOnNhd ℂ (WP.Analysis.complexSmallW P R g d) Ω)
    (T : ℝ) (hT : 1≤T)
    (hsb : ∀g:ℕ,∀d:List ℕ,Stable g d.length → ∀z∈Ω,
      ‖WP.Analysis.complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length))
    (M : ℝ) (hM1 : 1≤M) (K : ℕ) (F : ℂ → HierarchyJet) (e : WP.HigherOrder.Series)
    (he : ∀ n,0≤PowerSeries.coeff n e)
    (hprofile : ∀ z∈Ω,∀ i≤K-1,∀ d : List ℕ,1≤d.length →
      ‖PowerSeries.coeff i ((F z).profile d)‖≤(profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)
    (hpa : ∀ d : List ℕ,1≤d.length → AnalyticCoefficients Ω (K-1) (fun z=>(F z).profile d))
    (hca : ∀ p,AnalyticCoefficients Ω (K-1) (fun z=>(F z).cusp p))
    (hga : ∀ p,AnalyticCoefficients Ω (K-1) (fun z=>(F z).genus p)) (t : ℕ) (d : List ℕ) :
    AnalyticCoefficients Ω K (fun z=>separatingSeries P R z (F z) K t d) := by
  unfold separatingSeries
  apply AnalyticCoefficients.sum
  intro g hgK
  apply AnalyticCoefficients.sum
  intro I hId
  by_cases hs : Stable g (I.card+1) ∧ 2≤2*g+I.card ∧ 2*g+I.card≤K
  · simp only [ite_eq_left hs]
    obtain ⟨B,hB,hsmall⟩ := selected_smallW_uniform_bound Ω P R T hT hsb g d I
      (Finset.mem_powerset.mp hId) hs.1
    let G : ℂ → Series := fun z=>coefficientSum (fun l=>
      PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
        ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P R z g (u::selectedNat d I))*
          complexityShift ((2*g+I.card:ℕ):ℂ)
            ((F z).profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))
    have hG : AnalyticCoefficients Ω (K-(2*g+I.card)) G :=
      separating_kernel_analyticCoefficients Ω hΩ P R ρ C hρ hC hwa hwg M hM1 K F e he hprofile hpa
        g t d I hs.2.1 hs.2.2 B hB hsmall (fun u=>hsa g (u::selectedNat d I))
    have hb := ratioSeries_mul_analyticCoefficients_loss Ω R hA (K-(2*g+I.card)) F
      (fun p=>(hca p).mono (by omega)) (fun p=>(hga p).mono (by omega)) G hG (d.length+1) g I.card
    rw [Nat.sub_add_cancel hs.2.2] at hb
    simpa only [G,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hb
  · simpa only [ite_eq_right hs] using AnalyticCoefficients.const (Ω:=Ω) (N:=K) 0

end WP.HigherOrder.ComplexCanonical
