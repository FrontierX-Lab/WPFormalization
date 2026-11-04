import WPFormalization.HigherOrder.ComplexSeparatingAnalytic
/-! The genuine analytic part of the triangular induction. Uniform bounds for
old coefficients and for the newly constructed profile are the quantitative
induction data. No future scalar coefficient is assumed analytic. The theorem
is a local proof step, not the unproved all-order majorant conclusion. -/
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
noncomputable section
open Set PowerSeries
namespace WP.HigherOrder.ComplexCanonical

lemma nextJet_analytic_step (Ω : Set ℂ) (hΩ : IsOpen Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (ρ C : ℝ) (hρ : 1<ρ) (hC : 0≤C)
    (hwa : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexWeightCoeff R l) Ω)
    (hwg : ∀ l z,z∈Ω → ‖WP.Analysis.complexWeightCoeff R l z‖≤C/ρ^l)
    (hba : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexDilatonCoefficient R l) Ω)
    (hbg : ∀ l z,z∈Ω → ‖WP.Analysis.complexDilatonCoefficient R l z‖≤C/ρ^l)
    (hA : AnalyticOnNhd ℂ (kernelA R) Ω) (hA0 : ∀ z∈Ω,kernelA R z≠0)
    (hsa : ∀ g d,AnalyticOnNhd ℂ (WP.Analysis.complexSmallW P R g d) Ω)
    (T : ℝ) (hT : 1≤T)
    (hsb : ∀g:ℕ,∀d:List ℕ,Stable g d.length → ∀z∈Ω,
      ‖WP.Analysis.complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length))
    (M : ℝ) (hM1 : 1≤M) (j : ℕ) (F : ℂ → HierarchyJet) (e e' : WP.HigherOrder.Series)
    (he : ∀ n,0≤PowerSeries.coeff n e) (he' : ∀ n,0≤PowerSeries.coeff n e')
    (hprofile : ∀ z∈Ω,∀ i≤j,∀ d : List ℕ,1≤d.length →
      ‖PowerSeries.coeff i ((F z).profile d)‖≤(profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)
    (hnewProfile : ∀ z∈Ω,∀ i≤j+1,∀ d : List ℕ,1≤d.length →
      ‖PowerSeries.coeff i ((nextJet P R z (j+1) (F z)).profile d)‖≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e')
    (hpa : ∀ d,AnalyticCoefficients Ω j (fun z=>(F z).profile d))
    (hca : ∀ p,AnalyticCoefficients Ω j (fun z=>(F z).cusp p))
    (hga : ∀ p,AnalyticCoefficients Ω j (fun z=>(F z).genus p))
    (hunit : ∀ z∈Ω,∀ p,PowerSeries.constantCoeff ((F z).cusp p)=1) :
    (∀ d,AnalyticCoefficients Ω (j+1) (fun z=>(nextJet P R z (j+1) (F z)).profile d)) ∧
    (∀ p,AnalyticCoefficients Ω (j+1) (fun z=>(nextJet P R z (j+1) (F z)).cusp p)) ∧
    (∀ p,AnalyticCoefficients Ω (j+1) (fun z=>(nextJet P R z (j+1) (F z)).genus p)) := by
  have hmerger (t : ℕ) (d : List ℕ) :=
    mergerSeries_analyticCoefficients Ω hΩ R ρ C hρ hC hwa hwg M hM1 j F e he hprofile
      (fun d _=>hpa d) hA hca t d
  have hnonsep (t : ℕ) (d : List ℕ) :=
    nonseparatingSeries_analyticCoefficients Ω hΩ R ρ C hρ hC hwa hwg M hM1 j F e he hprofile
      (fun d _=>hpa d) hA hca hga t d
  have hsep (t : ℕ) (d : List ℕ) :=
    separatingSeries_analyticCoefficients Ω hΩ P R ρ C hρ hC hwa hwg hA hsa T hT hsb M hM1 (j+1) F e he
      (by simpa only [Nat.add_sub_cancel] using hprofile)
      (by simpa only [Nat.add_sub_cancel] using (fun d (_ : 1≤d.length)=>hpa d))
      (by simpa only [Nat.add_sub_cancel] using hca)
      (by simpa only [Nat.add_sub_cancel] using hga) t d
  have hinc (i : ℕ) (d : List ℕ) :
      AnalyticOnNhd ℂ (fun z=>adjacentCoefficient P R z (F z) (j+1) i d) Ω := by
    let t := d[i]!
    let tail := d.eraseIdx i
    have hsum := ((hmerger t tail).add (hnonsep t tail)).add (hsep t tail)
    have hc := hsum (j+1) le_rfl
    have heq : (fun z=>adjacentCoefficient P R z (F z) (j+1) i d)=
        -(fun z=>PowerSeries.coeff (j+1) (mergerSeries R z (F z) t tail+
          nonseparatingSeries R z (F z) t tail+separatingSeries P R z (F z) (j+1) t tail)) := by
      funext z
      rfl
    rw [heq]
    exact fun z hz=>(hc z hz).neg
  have hpath (d : List ℕ) : AnalyticOnNhd ℂ (fun z=>profileAtOrder P R z (F z) (j+1) d) Ω := by
    intro z hz
    unfold profileAtOrder
    apply Finset.analyticAt_fun_sum
    intro i hi
    apply Finset.analyticAt_fun_sum
    intro t ht
    exact hinc i (beforeCoordinate d i t) z hz
  let profiles : ℂ → List ℕ → Series := fun z d=>
    setCoeff ((F z).profile d) (j+1) (profileAtOrder P R z (F z) (j+1) d)
  have hp : ∀ d,AnalyticCoefficients Ω (j+1) (fun z=>profiles z d) :=
    fun d=>(hpa d).setCoeff_succ (hpath d)
  let PF : ℂ → HierarchyJet := fun z=>⟨profiles z,(F z).cusp,(F z).genus⟩
  have hpc : ∀ p,AnalyticCoefficients Ω (j+1) (fun z=>cuspSeries R z (profiles z) p) := by
    intro p
    exact cuspSeries_analyticCoefficients Ω hΩ R ρ C hρ hC hba hbg hA hA0 M hM1 (j+1) PF e' he'
      (fun z hz i hi d hd=>hnewProfile z hz i hi d hd) (fun d _=>hp d) p
  let cusps : ℂ → ℕ → Series := fun z p=>setCoeff ((F z).cusp p) (j+1)
    (PowerSeries.coeff (j+1) (cuspSeries R z (profiles z) p))
  have hc : ∀ p,AnalyticCoefficients Ω (j+1) (fun z=>cusps z p) :=
    fun p=>(hca p).setCoeff_succ (hpc p (j+1) le_rfl)
  have hcunit : ∀ z∈Ω,∀ p,PowerSeries.constantCoeff (cusps z p)=1 := by
    intro z hz p
    dsimp only [cusps]
    rw [setCoeff_constant _ _ _ (by omega)]
    exact hunit z hz p
  have hpg : ∀ p,AnalyticCoefficients Ω (j+1)
      (fun z=>genusSeries P R z (F z) (profiles z) (j+1) p) :=
    genusSeries_analyticCoefficients Ω P R hA hsa j F profiles hp hca hga
  let highGenus : ℂ → ℕ → Series := fun z p=>setCoeff ((F z).genus p) (j+1)
    (PowerSeries.coeff (j+1) (genusSeries P R z (F z) (profiles z) (j+1) p))
  have hg : ∀ p,AnalyticCoefficients Ω (j+1) (fun z=>highGenus z p) :=
    fun p=>(hga p).setCoeff_succ (hpg p (j+1) le_rfl)
  let genus₁ : ℂ → Series := fun z=>setCoeff ((F z).genus 1) (j+1)
    (PowerSeries.coeff (j+1) (descendGenus (cusps z) (highGenus z 2) 1))
  have hg₁ : AnalyticCoefficients Ω (j+1) genus₁ :=
    (hga 1).setCoeff_succ ((descendGenus_analyticCoefficients Ω (j+1) cusps
      (fun z=>highGenus z 2) 1 hc (hg 2)
      (by intro z hz;rw [hcunit z hz 1];exact one_ne_zero)) (j+1) le_rfl)
  let genus₀ : ℂ → Series := fun z=>setCoeff ((F z).genus 0) (j+1)
    (PowerSeries.coeff (j+1) (descendGenus (cusps z) (genus₁ z) 0))
  have hg₀ : AnalyticCoefficients Ω (j+1) genus₀ :=
    (hga 0).setCoeff_succ ((descendGenus_analyticCoefficients Ω (j+1) cusps genus₁ 0 hc hg₁
      (by intro z hz;rw [hcunit z hz 0];exact one_ne_zero)) (j+1) le_rfl)
  change (∀d,AnalyticCoefficients Ω (j+1) (fun z=>profiles z d)) ∧
    (∀p,AnalyticCoefficients Ω (j+1) (fun z=>cusps z p)) ∧
    (∀p,AnalyticCoefficients Ω (j+1)
      (fun z=>if p=0 then genus₀ z else if p=1 then genus₁ z else highGenus z p))
  refine ⟨hp,hc,?_⟩
  intro p
  by_cases hp0 : p=0
  · simpa only [ite_eq_left hp0] using hg₀
  · by_cases hp1 : p=1
    · simpa only [ite_eq_right hp0,ite_eq_left hp1] using hg₁
    · simpa only [ite_eq_right hp0,ite_eq_right hp1] using hg p


section GlobalAnalytic
variable (Ω : Set ℂ) (hΩ : IsOpen Ω) (P : PsiTheory) (R : ℂ → ℂ)
variable (ρ C : ℝ) (hρ : 1<ρ) (hC : 0≤C)
variable (hwa : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexWeightCoeff R l) Ω)
variable (hwg : ∀ l z,z∈Ω → ‖WP.Analysis.complexWeightCoeff R l z‖≤C/ρ^l)
variable (hba : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexDilatonCoefficient R l) Ω)
variable (hbg : ∀ l z,z∈Ω → ‖WP.Analysis.complexDilatonCoefficient R l z‖≤C/ρ^l)
variable (hA : AnalyticOnNhd ℂ (kernelA R) Ω) (hA0 : ∀ z∈Ω,kernelA R z≠0)
variable (hsa : ∀ g d,AnalyticOnNhd ℂ (WP.Analysis.complexSmallW P R g d) Ω)
variable (T : ℝ) (hT : 1≤T)
variable (hsb : ∀g:ℕ,∀d:List ℕ,Stable g d.length → ∀z∈Ω,
  ‖WP.Analysis.complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length))
variable (M : ℝ) (hM1 : 1≤M) (e : WP.HigherOrder.Series) (he : ∀ n,0≤PowerSeries.coeff n e)
variable (hprofile : ∀ i,∀ d : List ℕ,1≤d.length → ∀ z∈Ω,
  ‖profileCoefficient P R z d i‖≤(profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e)

include hΩ hρ hC hwa hwg hba hbg hA hA0 hsa hT hsb hM1 he hprofile in
lemma hierarchyJet_analytic_of_profile_majorant : ∀n:ℕ,
    (∀d,AnalyticCoefficients Ω n (fun z=>(hierarchyJet P R z n).profile d)) ∧
    (∀p,AnalyticCoefficients Ω n (fun z=>(hierarchyJet P R z n).cusp p)) ∧
    (∀p,AnalyticCoefficients Ω n (fun z=>(hierarchyJet P R z n).genus p)) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun _=>AnalyticCoefficients.const 1,fun _=>AnalyticCoefficients.const 1,
      fun _=>AnalyticCoefficients.const 1⟩
  | succ n ih =>
    have hold : ∀ z∈Ω,∀i≤n,∀d:List ℕ,1≤d.length →
        ‖PowerSeries.coeff i ((hierarchyJet P R z n).profile d)‖≤
          (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e := by
      intro z hz i hi d hd
      rw [hierarchy_profile_stable P R z d n i hi]
      exact hprofile i d hd z hz
    have hnew : ∀ z∈Ω,∀i≤n+1,∀d:List ℕ,1≤d.length →
        ‖PowerSeries.coeff i ((nextJet P R z (n+1) (hierarchyJet P R z n)).profile d)‖≤
          (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e := by
      intro z hz i hi d hd
      change ‖PowerSeries.coeff i ((hierarchyJet P R z (n+1)).profile d)‖≤_
      rw [hierarchy_profile_stable P R z d (n+1) i hi]
      exact hprofile i d hd z hz
    have hstep := nextJet_analytic_step Ω hΩ P R ρ C hρ hC hwa hwg hba hbg hA hA0 hsa T hT hsb
      M hM1 n (fun z=>hierarchyJet P R z n) e e he he hold hnew ih.1 ih.2.1 ih.2.2
      (fun z _ p=>(hierarchy_unit_constants P R z n).2.1 p)
    exact hstep

include hΩ hρ hC hwa hwg hba hbg hA hA0 hsa hT hsb hM1 he hprofile in
lemma canonical_holomorphy_of_profile_majorant : ∀j:ℕ,
    (∀d,AnalyticOnNhd ℂ (fun z=>profileCoefficient P R z d j) Ω) ∧
    (∀p,AnalyticOnNhd ℂ (fun z=>cuspCoefficient P R z p j) Ω) ∧
    (∀p,AnalyticOnNhd ℂ (fun z=>genusCoefficient P R z p j) Ω) := by
  intro j
  have hstage := hierarchyJet_analytic_of_profile_majorant Ω hΩ P R ρ C hρ hC hwa hwg hba hbg
    hA hA0 hsa T hT hsb M hM1 e he hprofile j
  exact ⟨fun d=>hstage.1 d j le_rfl,fun p=>hstage.2.1 p j le_rfl,fun p=>hstage.2.2 p j le_rfl⟩

end GlobalAnalytic

lemma canonical_holomorphy_of_exponential_profile_bound (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (P : PsiTheory) (R : ℂ → ℂ) (ρ C : ℝ) (hρ : 1<ρ) (hC : 0≤C)
    (hwa : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexWeightCoeff R l) Ω)
    (hwg : ∀ l z,z∈Ω → ‖WP.Analysis.complexWeightCoeff R l z‖≤C/ρ^l)
    (hba : ∀ l,AnalyticOnNhd ℂ (WP.Analysis.complexDilatonCoefficient R l) Ω)
    (hbg : ∀ l z,z∈Ω → ‖WP.Analysis.complexDilatonCoefficient R l z‖≤C/ρ^l)
    (hA : AnalyticOnNhd ℂ (kernelA R) Ω) (hA0 : ∀ z∈Ω,kernelA R z≠0)
    (hsa : ∀ g d,AnalyticOnNhd ℂ (WP.Analysis.complexSmallW P R g d) Ω)
    (T : ℝ) (hT : 1≤T)
    (hsb : ∀g:ℕ,∀d:List ℕ,Stable g d.length → ∀z∈Ω,
      ‖WP.Analysis.complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length))
    (M : ℝ) (hM1 : 1≤M) (C₁ B₁ : ℝ) (hC₁ : 0≤C₁) (hB₁ : 0≤B₁)
    (hprofile : ∀i:ℕ,∀d:List ℕ,1≤d.length → ∀z∈Ω,
      ‖profileCoefficient P R z d i‖≤C₁*B₁^i*(profileOrderWeight M i d)^(2*i)) :
    ∀j:ℕ,(∀d,AnalyticOnNhd ℂ (fun z=>profileCoefficient P R z d j) Ω) ∧
      (∀p,AnalyticOnNhd ℂ (fun z=>cuspCoefficient P R z p j) Ω) ∧
      (∀p,AnalyticOnNhd ℂ (fun z=>genusCoefficient P R z p j) Ω) := by
  let e : WP.HigherOrder.Series := PowerSeries.mk (fun i=>C₁*B₁^i)
  have he : ∀i,0≤PowerSeries.coeff i e := by
    intro i
    simp only [e,PowerSeries.coeff_mk]
    positivity
  apply canonical_holomorphy_of_profile_majorant Ω hΩ P R ρ C hρ hC hwa hwg hba hbg hA hA0 hsa
    T hT hsb M hM1 e he
  intro i d hd z hz
  simpa only [e,PowerSeries.coeff_mk,mul_comm] using hprofile i d hd z hz

end WP.HigherOrder.ComplexCanonical
