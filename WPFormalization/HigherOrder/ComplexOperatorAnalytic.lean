import WPFormalization.HigherOrder.ComplexCoefficientAnalytic
import WPFormalization.HigherOrder.ComplexLinearMajorant
/-! Normal convergence and holomorphy for the actual complex linear operators.
The displayed lower-order profile bounds are local induction hypotheses. They
are not asserted as assumptions for any final all-order paper theorem. -/
set_option maxHeartbeats 800000
noncomputable section
open Set PowerSeries
namespace WP.HigherOrder.ComplexCanonical
lemma merger_shifted_profile_norm_polynomial (M : ℝ) (hM1 : 1≤M) (j : ℕ) (F : HierarchyJet) (e : WP.HigherOrder.Series)
    (he : ∀n:ℕ,0≤PowerSeries.coeff n e)
    (hprofile : ∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→‖PowerSeries.coeff i (F.profile d)‖≤
      (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)
    (t : ℕ) (d : List ℕ) (k : ℕ) (hk : k<d.length) (n : ℕ) (hn : n≤j) (l : ℕ) :
    ‖PowerSeries.coeff n (if 1≤t+d[k]!+l then
      complexityShift 1 (F.profile (mergerProfile t d l k)) else 0)‖≤
      PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)*
        (profileOrderWeight M (j+1) (t::d)+l+1)^(2*n) := by
  have hM0:0≤M:=by linarith
  let S:=profileOrderWeight M (j+1) (t::d)
  have hSJ:((j+1:ℕ):ℝ)≤S := by
    have hj:=mul_le_mul_of_nonneg_right hM1 (show (0:ℝ)≤((j+1:ℕ):ℝ) from Nat.cast_nonneg (j+1))
    dsimp [S,profileOrderWeight]
    nlinarith [show (0:ℝ)≤(t::d).sum from Nat.cast_nonneg _,show (0:ℝ)≤(t::d).length from Nat.cast_nonneg _]
  have hEN : ∀i:ℕ,0≤PowerSeries.coeff i ((PowerSeries.exp ℝ)*e):=coeff_mul_nonneg exp_coeff_nonneg he
  let L:ℕ→Series:=fun l=>if 1≤t+d[k]!+l then complexityShift 1 (F.profile (mergerProfile t d l k)) else 0
  have hL (l:ℕ) : ‖PowerSeries.coeff n (L l)‖≤
      PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)*(S+l+1)^(2*n) := by
    have hSl : ((j+1:ℕ):ℝ)≤S+l+1:=by linarith [Nat.cast_nonneg (α:=ℝ) l]
    have hSl0:0≤S+l+1:=le_trans (Nat.cast_nonneg (j+1)) hSl
    by_cases hg:1≤t+d[k]!+l
    · dsimp [L]
      rw [ite_eq_left hg]
      have hshift:=complex_shift_coeff_exponential_majorant 1 (S+l+1)
        (F.profile (mergerProfile t d l k)) (fun i=>PowerSeries.coeff i e) n (j+1)
        (by omega) (by norm_num) hSl he (by
          intro i hi
          have hlen:(mergerProfile t d l k).length=d.length:=by
            simp only [mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hk]
            omega
          have hp:=hprofile i (hi.trans hn) (mergerProfile t d l k) (by rw [hlen];omega)
          have hw:=merger_order_weight M hM0 i (j+1) t l k d (by omega) hk hg
          have hw0:0≤profileOrderWeight M i (mergerProfile t d l k):=by unfold profileOrderWeight;positivity
          have hw':profileOrderWeight M i (mergerProfile t d l k)≤S+l+1:=by dsimp [S];linarith
          simpa only [mul_comm] using hp.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw' (2*i)) (he i)))
      have hemk : PowerSeries.mk (fun i=>PowerSeries.coeff i e)=e := by ext i;simp
      rw [hemk] at hshift
      simpa only [mul_comm,complexityShift,shiftVariable] using hshift
    · simp only [L,ite_eq_right hg,map_zero,norm_zero]
      exact mul_nonneg (hEN n) (pow_nonneg hSl0 _)
  exact hL l

lemma contraction_shifted_profile_norm_polynomial (M : ℝ) (hM1 : 1≤M) (j : ℕ) (F : HierarchyJet) (e : WP.HigherOrder.Series)
    (he : ∀n:ℕ,0≤PowerSeries.coeff n e)
    (hprofile : ∀i:ℕ,i≤j→∀d:List ℕ,1≤d.length→‖PowerSeries.coeff i (F.profile d)‖≤
      (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)
    (t : ℕ) (d : List ℕ) (n : ℕ) (hn : n≤j) (l : ℕ) :
    ‖PowerSeries.coeff n (∑u∈Finset.range (t+l-1),
      complexityShift 1 (F.profile (contractionProfile t d l u)))‖≤
      PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)*
        (profileOrderWeight M (j+1) (t::d)+l+1)^(2*n+1) := by
  have hM0:0≤M:=by linarith
  let S:=profileOrderWeight M (j+1) (t::d)
  have hSJ:((j+1:ℕ):ℝ)≤S := by
    have hj:=mul_le_mul_of_nonneg_right hM1 (show (0:ℝ)≤((j+1:ℕ):ℝ) from Nat.cast_nonneg (j+1))
    dsimp [S,profileOrderWeight]
    nlinarith [show (0:ℝ)≤(t::d).sum from Nat.cast_nonneg _,show (0:ℝ)≤(t::d).length from Nat.cast_nonneg _]
  have hEN : ∀i:ℕ,0≤PowerSeries.coeff i ((PowerSeries.exp ℝ)*e):=coeff_mul_nonneg exp_coeff_nonneg he
  let L:ℕ→Series:=fun l=>∑u∈Finset.range (t+l-1),complexityShift 1 (F.profile (contractionProfile t d l u))
  have hL (l:ℕ) : ‖PowerSeries.coeff n (L l)‖≤
      PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)*(S+l+1)^(2*n+1) := by
    have hSl : ((j+1:ℕ):ℝ)≤S+l+1:=by linarith [Nat.cast_nonneg (α:=ℝ) l]
    have hSl0:0≤S+l+1:=(Nat.cast_nonneg (j+1)).trans hSl
    have hpoint (u:ℕ) (hu:u∈Finset.range (t+l-1)) :
        ‖PowerSeries.coeff n (complexityShift 1 (F.profile (contractionProfile t d l u)))‖≤
        (S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e) := by
      have hshift:=complex_shift_coeff_exponential_majorant 1 (S+l+1)
        (F.profile (contractionProfile t d l u)) (fun i=>PowerSeries.coeff i e) n (j+1)
        (by omega) (by norm_num) hSl he (by
          intro i hi
          have hp:=hprofile i (hi.trans hn) (contractionProfile t d l u) (by simp [contractionProfile])
          have hw:=handle_order_weight M hM0 i (j+1) t l u d (by omega) (Finset.mem_range.mp hu)
          have hw0:0≤profileOrderWeight M i (contractionProfile t d l u):=by unfold profileOrderWeight;positivity
          have hw':profileOrderWeight M i (contractionProfile t d l u)≤S+l+1:=by dsimp [S];linarith
          simpa only [mul_comm] using hp.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw' (2*i)) (he i)))
      have hemk:PowerSeries.mk (fun i=>PowerSeries.coeff i e)=e:=by ext i;simp
      rw [hemk] at hshift
      simpa only[complexityShift,shiftVariable] using hshift
    simp only [L,map_sum]
    apply (norm_sum_le _ _).trans
    calc _≤∑u∈Finset.range (t+l-1),(S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e) :=
           Finset.sum_le_sum hpoint
         _=((t+l-1:ℕ):ℝ)*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)) := by
           simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
         _≤(S+l+1)*((S+l+1)^(2*n)*PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)) :=
           mul_le_mul_of_nonneg_right
             ((pair_count_le_order_weight M hM0 (j+1) t l d).trans (by dsimp [S];linarith))
             (mul_nonneg (pow_nonneg hSl0 _) (hEN n))
         _=_:=by rw [pow_succ];ring
  exact hL l


lemma AnalyticCoefficients.X_mul {Ω : Set ℂ} {N : ℕ} {F : ℂ → Series}
    (hF : AnalyticCoefficients Ω N F) :
    AnalyticCoefficients Ω (N+1) (fun z=>PowerSeries.X*F z) := by
  intro n hn
  cases n with
  | zero =>
    have he : (fun z=>PowerSeries.coeff 0 (PowerSeries.X*F z))=(fun _ : ℂ=>0) := by
      funext z
      simp only [PowerSeries.coeff_zero_X_mul]
    rw [he]
    exact analyticOnNhd_const
  | succ n =>
    simpa only [PowerSeries.coeff_succ_X_mul] using hF n (by omega)

section LinearAnalytic
variable (Ω : Set ℂ) (hΩ : IsOpen Ω) (R : ℂ → ℂ) (ρ C : ℝ) (hρ : 1<ρ) (hC : 0≤C)
variable (hwa : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexWeightCoeff R l) Ω)
variable (hwg : ∀ l z,z∈Ω → ‖WP.Analysis.complexWeightCoeff R l z‖≤C/ρ^l)
variable (M : ℝ) (hM1 : 1≤M) (j : ℕ) (F : ℂ → HierarchyJet) (e : WP.HigherOrder.Series)
variable (he : ∀ n,0≤PowerSeries.coeff n e)
variable (hprofile : ∀ z∈Ω,∀ i≤j,∀ d : List ℕ,1≤d.length →
  ‖PowerSeries.coeff i ((F z).profile d)‖≤(profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)
variable (hpa : ∀ d : List ℕ,1≤d.length → AnalyticCoefficients Ω j (fun z=>(F z).profile d))

include hΩ hρ hC hwa hwg hM1 he hprofile hpa in
lemma merger_kernel_analyticCoefficients (t : ℕ) (d : List ℕ) (k : ℕ) (hk : k<d.length) :
    AnalyticCoefficients Ω j (fun z=>coefficientSum (fun l=>if 1≤t+d[k]!+l then
      PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
        complexityShift 1 ((F z).profile (mergerProfile t d l k)) else 0)) := by
  let L : ℕ → ℂ → Series := fun l z=>if 1≤t+d[k]!+l then
    complexityShift 1 ((F z).profile (mergerProfile t d l k)) else 0
  have hLa : ∀ l,AnalyticCoefficients Ω j (L l) := by
    intro l
    by_cases hg : 1≤t+d[k]!+l
    · dsimp only [L]
      simp only [ite_eq_left hg]
      apply (hpa (mergerProfile t d l k) ?_).shift
      have hlen : (mergerProfile t d l k).length=d.length := by
        simp only [mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hk]
        omega
      rw [hlen]
      omega
    · simpa only [L,ite_eq_right hg] using AnalyticCoefficients.const (Ω:=Ω) (N:=j) 0
  have hLb : ∀ n≤j,∃ (B S : ℝ) (q : ℕ),0≤B ∧ 0≤S ∧
      ∀ l z,z∈Ω → ‖PowerSeries.coeff n (L l z)‖≤B*(S+l+1)^q := by
    intro n hn
    refine ⟨PowerSeries.coeff n ((PowerSeries.exp ℝ)*e),profileOrderWeight M (j+1) (t::d),2*n,
      coeff_mul_nonneg exp_coeff_nonneg he n,?_,?_⟩
    · unfold profileOrderWeight
      have hM0 : 0≤M := by linarith
      positivity
    · intro l z hz
      exact merger_shifted_profile_norm_polynomial M hM1 j (F z) e he (hprofile z hz) t d k hk n hn l
  have hsum := AnalyticCoefficients.geometric_weighted_coefficientSum hΩ ρ C hρ hC
    (WP.Analysis.complexWeightCoeff R) hwa hwg L hLa hLb
  have hs : (fun z=>coefficientSum (fun l=>if 1≤t+d[k]!+l then
      PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
        complexityShift 1 ((F z).profile (mergerProfile t d l k)) else 0))=
      (fun z=>coefficientSum (fun l=>PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*L l z)) := by
    funext z
    apply congrArg coefficientSum
    funext l
    dsimp only [L]
    split_ifs <;>simp
  rw [hs]
  exact hsum.2

include hΩ hρ hC hwa hwg hM1 he hprofile hpa in
lemma handle_kernel_analyticCoefficients (t : ℕ) (d : List ℕ) :
    AnalyticCoefficients Ω j (fun z=>coefficientSum (fun l=>
      PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
        ∑ u∈Finset.range (t+l-1),complexityShift 1 ((F z).profile (contractionProfile t d l u)))) := by
  let L : ℕ → ℂ → Series := fun l z=>
    ∑ u∈Finset.range (t+l-1),complexityShift 1 ((F z).profile (contractionProfile t d l u))
  have hLa : ∀ l,AnalyticCoefficients Ω j (L l) := by
    intro l
    apply AnalyticCoefficients.sum
    intro u hu
    exact (hpa (contractionProfile t d l u) (by simp [contractionProfile])).shift 1
  have hLb : ∀ n≤j,∃ (B S : ℝ) (q : ℕ),0≤B ∧ 0≤S ∧
      ∀ l z,z∈Ω → ‖PowerSeries.coeff n (L l z)‖≤B*(S+l+1)^q := by
    intro n hn
    refine ⟨PowerSeries.coeff n ((PowerSeries.exp ℝ)*e),profileOrderWeight M (j+1) (t::d),2*n+1,
      coeff_mul_nonneg exp_coeff_nonneg he n,?_,?_⟩
    · unfold profileOrderWeight
      have hM0 : 0≤M := by linarith
      positivity
    · intro l z hz
      exact contraction_shifted_profile_norm_polynomial M hM1 j (F z) e he (hprofile z hz) t d n hn l
  exact (AnalyticCoefficients.geometric_weighted_coefficientSum hΩ ρ C hρ hC
    (WP.Analysis.complexWeightCoeff R) hwa hwg L hLa hLb).2

variable (hA : AnalyticOnNhd ℂ (kernelA R) Ω)
variable (hca : ∀ p,AnalyticCoefficients Ω j (fun z=>(F z).cusp p))
variable (hga : ∀ p,AnalyticCoefficients Ω j (fun z=>(F z).genus p))

include hΩ hρ hC hwa hwg hM1 he hprofile hpa hA hca in
lemma mergerSeries_analyticCoefficients (t : ℕ) (d : List ℕ) :
    AnalyticCoefficients Ω (j+1) (fun z=>mergerSeries R z (F z) t d) := by
  let H : ℂ → Series := fun z=>∑ k∈Finset.range d.length,PowerSeries.C (2*(d[k]!:ℂ)+1)*
    coefficientSum (fun l=>if 1≤t+d[k]!+l then PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
      complexityShift 1 ((F z).profile (mergerProfile t d l k)) else 0)
  have hH : AnalyticCoefficients Ω j H := by
    apply AnalyticCoefficients.sum
    intro k hk
    exact (AnalyticCoefficients.const (PowerSeries.C (2*(d[k]!:ℂ)+1))).mul
      (merger_kernel_analyticCoefficients Ω hΩ R ρ C hρ hC hwa hwg M hM1 j F e he hprofile hpa t d k
        (Finset.mem_range.mp hk))
  have hrest : AnalyticCoefficients Ω j (fun z=>
      (1-PowerSeries.C 1*PowerSeries.X)⁻¹*(complexityShift 1 ((F z).cusp d.length)*H z)) :=
    (AnalyticCoefficients.const _).mul (((hca d.length).shift 1).mul hH)
  have hmain := (AnalyticCoefficients.C (N:=j+1) hA).mul hrest.X_mul
  have hs : (fun z=>mergerSeries R z (F z) t d)=(fun z=>PowerSeries.C (kernelA R z)*
      (PowerSeries.X*((1-PowerSeries.C 1*PowerSeries.X)⁻¹*
        (complexityShift 1 ((F z).cusp d.length)*H z)))) := by
    funext z
    dsimp only [mergerSeries,H,mergerProfile,shiftVariable]
    ring
  rw [hs]
  exact hmain

include hΩ hρ hC hwa hwg hM1 he hprofile hpa hA hca hga in
lemma nonseparatingSeries_analyticCoefficients (t : ℕ) (d : List ℕ) :
    AnalyticCoefficients Ω (j+1) (fun z=>nonseparatingSeries R z (F z) t d) := by
  let H : ℂ → Series := fun z=>coefficientSum (fun l=>
    PowerSeries.C (WP.Analysis.complexWeightCoeff R l z)*
      ∑ u∈Finset.range (t+l-1),complexityShift 1 ((F z).profile (contractionProfile t d l u)))
  have hH : AnalyticCoefficients Ω j H :=
    handle_kernel_analyticCoefficients Ω hΩ R ρ C hρ hC hwa hwg M hM1 j F e he hprofile hpa t d
  have hrest : AnalyticCoefficients Ω j (fun z=>(1-PowerSeries.C 1*PowerSeries.X)⁻¹*
      (complexityShift 1 ((F z).cusp (d.length+2))*((F z).genus (d.length+1)*H z))) :=
    (AnalyticCoefficients.const _).mul (((hca (d.length+2)).shift 1).mul ((hga (d.length+1)).mul hH))
  have h2A : AnalyticOnNhd ℂ (fun z=>(2:ℂ)*kernelA R z) Ω :=
    fun z hz=>analyticAt_const.mul (hA z hz)
  have hmain := (AnalyticCoefficients.C (N:=j+1) h2A).mul hrest.X_mul
  have hs : (fun z=>nonseparatingSeries R z (F z) t d)=
      (fun z=>PowerSeries.C (2*kernelA R z)*(PowerSeries.X*((1-PowerSeries.C 1*PowerSeries.X)⁻¹*
        (complexityShift 1 ((F z).cusp (d.length+2))*((F z).genus (d.length+1)*H z))))) := by
    funext z
    dsimp only [nonseparatingSeries,H,contractionProfile,shiftVariable]
    ring
  rw [hs]
  exact hmain

end LinearAnalytic

lemma cusp_shifted_profile_norm_polynomial (M : ℝ) (hM1 : 1≤M) (j : ℕ)
    (F : HierarchyJet) (e : WP.HigherOrder.Series) (he : ∀ n,0≤PowerSeries.coeff n e)
    (hprofile : ∀ i≤j,∀ d : List ℕ,1≤d.length →
      ‖PowerSeries.coeff i (F.profile d)‖≤(profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)
    (p n : ℕ) (hn : n≤j) (l : ℕ) :
    ‖PowerSeries.coeff n (complexityShift (-1) (F.profile ((l+1)::List.replicate p 0)))‖≤
      PowerSeries.coeff n ((PowerSeries.exp ℝ)*e)*(((p:ℝ)+M*(j+1)+2)+l+1)^(2*n) := by
  have hM0 : 0≤M := by linarith
  let S : ℝ := (p:ℝ)+M*(j+1)+2
  have hSl : ((j+1:ℕ):ℝ)≤S+l+1 := by
    have hm := mul_le_mul_of_nonneg_right hM1 (Nat.cast_nonneg (α:=ℝ) (j+1))
    dsimp only [S]
    norm_num only [Nat.cast_add,Nat.cast_one] at hm ⊢
    nlinarith [Nat.cast_nonneg (α:=ℝ) p,Nat.cast_nonneg (α:=ℝ) l]
  have hSl0 : 0≤S+l+1 := (Nat.cast_nonneg (j+1)).trans hSl
  have hshift := complex_shift_coeff_exponential_majorant (-1) (S+l+1)
    (F.profile ((l+1)::List.replicate p 0)) (fun i=>PowerSeries.coeff i e) n (j+1)
    (by omega) (by norm_num) hSl he (by
      intro i hi
      have hp := hprofile i (hi.trans hn) ((l+1)::List.replicate p 0) (by simp)
      have hm := mul_le_mul_of_nonneg_left
        (show (i:ℝ)≤((j+1:ℕ):ℝ) by exact_mod_cast (show i≤j+1 by omega)) hM0
      have hw : profileOrderWeight M i ((l+1)::List.replicate p 0)≤S+l+1 := by
        simp only [profileOrderWeight,List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,
          List.length_cons,List.length_replicate,Nat.cast_add,Nat.cast_one]
        dsimp only [S]
        norm_num only [Nat.cast_add,Nat.cast_one] at hm
        linarith
      have hw0 : 0≤profileOrderWeight M i ((l+1)::List.replicate p 0) := by
        unfold profileOrderWeight
        positivity
      simpa only [mul_comm] using hp.trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hw (2*i)) (he i)))
  have hemk : PowerSeries.mk (fun i=>PowerSeries.coeff i e)=e := by ext i;simp
  rw [hemk] at hshift
  simpa only [complexityShift,shiftVariable,S,mul_comm] using hshift

lemma cuspSeries_analyticCoefficients (Ω : Set ℂ) (hΩ : IsOpen Ω) (R : ℂ → ℂ)
    (ρ C : ℝ) (hρ : 1<ρ) (hC : 0≤C)
    (hba : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexDilatonCoefficient R l) Ω)
    (hbg : ∀ l z,z∈Ω → ‖WP.Analysis.complexDilatonCoefficient R l z‖≤C/ρ^l)
    (hA : AnalyticOnNhd ℂ (kernelA R) Ω) (hA0 : ∀ z∈Ω,kernelA R z≠0)
    (M : ℝ) (hM1 : 1≤M) (j : ℕ) (F : ℂ → HierarchyJet) (e : WP.HigherOrder.Series)
    (he : ∀ n,0≤PowerSeries.coeff n e)
    (hprofile : ∀ z∈Ω,∀ i≤j,∀ d : List ℕ,1≤d.length →
      ‖PowerSeries.coeff i ((F z).profile d)‖≤(profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)
    (hpa : ∀ d : List ℕ,1≤d.length → AnalyticCoefficients Ω j (fun z=>(F z).profile d))
    (p : ℕ) : AnalyticCoefficients Ω j (fun z=>cuspSeries R z (F z).profile p) := by
  let L : ℕ → ℂ → Series := fun l z=>complexityShift (-1) ((F z).profile ((l+1)::List.replicate p 0))
  have hLa : ∀ l,AnalyticCoefficients Ω j (L l) := by
    intro l
    exact (hpa ((l+1)::List.replicate p 0) (by simp)).shift (-1)
  have hLb : ∀ n≤j,∃ (B S : ℝ) (q : ℕ),0≤B ∧ 0≤S ∧
      ∀ l z,z∈Ω → ‖PowerSeries.coeff n (L l z)‖≤B*(S+l+1)^q := by
    intro n hn
    refine ⟨PowerSeries.coeff n ((PowerSeries.exp ℝ)*e),(p:ℝ)+M*(j+1)+2,2*n,
      coeff_mul_nonneg exp_coeff_nonneg he n,?_,?_⟩
    · have hM0 : 0≤M := by linarith
      positivity
    · intro l z hz
      exact cusp_shifted_profile_norm_polynomial M hM1 j (F z) e he (hprofile z hz) p n hn l
  have hweighta : ∀ l,AnalyticOnNhd ℂ (fun z=>bCoeff R z (l+1)) Ω := by
    intro l
    simpa only [bCoeff] using hba (l+1)
  have hweightg : ∀ l z,z∈Ω → ‖bCoeff R z (l+1)‖≤C/ρ^l := by
    intro l z hz
    calc
      _ ≤ C/ρ^(l+1) := hbg (l+1) z hz
      _ = (C/ρ^l)/ρ := by rw [pow_succ,div_mul_eq_div_div]
      _ ≤ C/ρ^l := div_le_self (by positivity) hρ.le
  have hsum := AnalyticCoefficients.geometric_weighted_coefficientSum hΩ ρ C hρ hC
    (fun l z=>bCoeff R z (l+1)) hweighta hweightg L hLa hLb
  have hAi : AnalyticOnNhd ℂ (fun z=>(kernelA R z)⁻¹) Ω :=
    fun z hz=>(hA z hz).inv (hA0 z hz)
  simpa only [cuspSeries,PowerSeries.C_inv] using (AnalyticCoefficients.C hAi).mul hsum.2


lemma AnalyticCoefficients.X_pow_mul {Ω : Set ℂ} {N : ℕ} {F : ℂ → Series}
    (hF : AnalyticCoefficients Ω N F) (q : ℕ) :
    AnalyticCoefficients Ω (N+q) (fun z=>PowerSeries.X^q*F z) := by
  intro n hn
  simp_rw [PowerSeries.coeff_X_pow_mul']
  by_cases hq : q≤n
  · simpa only [ite_eq_left hq] using hF (n-q) (by omega)
  · simpa only [ite_eq_right hq] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ=>(0:ℂ)) Ω)

lemma AnalyticCoefficients.setCoeff_succ {Ω : Set ℂ} {N : ℕ} {F : ℂ → Series}
    (hF : AnalyticCoefficients Ω N F) {a : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a Ω) :
    AnalyticCoefficients Ω (N+1) (fun z=>ComplexCanonical.setCoeff (F z) (N+1) (a z)) := by
  intro n hn
  by_cases h : n=N+1
  · subst n
    simpa only [ComplexCanonical.setCoeff,PowerSeries.coeff_mk,ite_true] using ha
  · simpa only [ComplexCanonical.setCoeff,PowerSeries.coeff_mk,ite_eq_right h] using hF n (by omega)

lemma ratioSeries_mul_analyticCoefficients_loss (Ω : Set ℂ) (R : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ (kernelA R) Ω) (N : ℕ) (F : ℂ → HierarchyJet)
    (hca : ∀ p,AnalyticCoefficients Ω N (fun z=>(F z).cusp p))
    (hga : ∀ p,AnalyticCoefficients Ω N (fun z=>(F z).genus p))
    (G : ℂ → Series) (hG : AnalyticCoefficients Ω N G) (p j s : ℕ) :
    AnalyticCoefficients Ω (N+(2*j+s)) (fun z=>ratioSeries R z (F z) p j s*G z) := by
  let r := 2*j+s
  let core : ℂ → Series := fun z=>
    (∏ a∈Finset.range r,complexityShift ((r:ℂ)-a) ((F z).cusp (p-s+a))*
      (1-PowerSeries.C ((r-a:ℕ):ℂ)*PowerSeries.X)⁻¹)*
      ∏ b∈Finset.range j,(F z).genus (p+2*b)
  have hcore : AnalyticCoefficients Ω N core := by
    apply AnalyticCoefficients.mul
    · apply AnalyticCoefficients.prod
      intro a ha
      exact ((hca (p-s+a)).shift ((r:ℂ)-a)).mul (AnalyticCoefficients.const _)
    · apply AnalyticCoefficients.prod
      intro b hb
      exact hga (p+2*b)
  have hmain := ((AnalyticCoefficients.C (N:=N+r) hA).pow r).mul ((hcore.mul hG).X_pow_mul r)
  have hs : (fun z=>ratioSeries R z (F z) p j s*G z)=
      (fun z=>(PowerSeries.C (kernelA R z))^r*(PowerSeries.X^r*(core z*G z))) := by
    funext z
    dsimp only [ratioSeries,core,r]
    ring
  rw [hs]
  exact hmain

lemma descendGenus_analyticCoefficients (Ω : Set ℂ) (N : ℕ)
    (cusps : ℂ → ℕ → Series) (next : ℂ → Series) (p : ℕ)
    (hc : ∀ q,AnalyticCoefficients Ω N (fun z=>cusps z q))
    (hg : AnalyticCoefficients Ω N next)
    (h0 : ∀ z∈Ω,PowerSeries.constantCoeff (cusps z p)≠0) :
    AnalyticCoefficients Ω N (fun z=>descendGenus (cusps z) (next z) p) :=
  ((hg.shift (-1)).mul (hc (p+2))).mul ((hc p).inv h0)

lemma genusSeries_analyticCoefficients (Ω : Set ℂ) (P : PsiTheory) (R : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ (kernelA R) Ω)
    (hsmall : ∀ g d,AnalyticOnNhd ℂ (WP.Analysis.complexSmallW P R g d) Ω)
    (j : ℕ) (F : ℂ → HierarchyJet) (profiles : ℂ → List ℕ → Series)
    (hp : ∀ d,AnalyticCoefficients Ω (j+1) (fun z=>profiles z d))
    (hc : ∀ p,AnalyticCoefficients Ω j (fun z=>(F z).cusp p))
    (hg : ∀ p,AnalyticCoefficients Ω j (fun z=>(F z).genus p)) (p : ℕ) :
    AnalyticCoefficients Ω (j+1) (fun z=>genusSeries P R z (F z) (profiles z) (j+1) p) := by
  unfold genusSeries
  apply AnalyticCoefficients.sub
  · exact hp _
  · apply AnalyticCoefficients.mul (AnalyticCoefficients.const _)
    apply AnalyticCoefficients.sum
    intro g hgj
    apply AnalyticCoefficients.sum
    intro s hsp
    by_cases hs : Stable g (s+2) ∧ 1≤2*g+s ∧ 2*g+s≤j+1
    · simp only [ite_eq_left hs]
      have hsa : AnalyticOnNhd ℂ (fun z=>(Nat.choose (p-2) s:ℂ)*smallW P R z g (List.replicate (s+2) 0)) Ω := by
        intro z hz
        exact analyticAt_const.mul (hsmall g (List.replicate (s+2) 0) z hz)
      apply (AnalyticCoefficients.C hsa).mul
      have hb := (ratioSeries_mul_analyticCoefficients_loss Ω R hA j F hc hg (fun _=>1)
        (AnalyticCoefficients.const _) p g s).mono (show j+1≤j+(2*g+s) by omega)
      simpa only [mul_one] using hb
    · simpa only [ite_eq_right hs] using AnalyticCoefficients.const (Ω:=Ω) (N:=j+1) 0

end WP.HigherOrder.ComplexCanonical
