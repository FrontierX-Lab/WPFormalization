import WPFormalization.Volumes.BoundaryPolynomial
import WPFormalization.Marked.ShiftedTransport
/-! The genuine finite shifted polynomial in Appendix F.1 and its uniform
profile estimates. Identification with geometric tight volumes is kept
separate and is not asserted by this module. -/
noncomputable section
namespace WP
open Set Filter
open scoped Topology
/-- The finite shifted-insertion polynomial on the right of Appendix F.1.
Its geometric tight-volume interpretation requires the classical transform;
this definition does not assert that unconstructed geometric bridge. -/
def tightShiftedPolynomial (P:PsiTheory) (g p:ℕ) (Y:ℝ) (L:Fin p→ℝ) : ℝ :=
  ∑d∈degreeTuples g p,shifted P g (List.ofFn d) Y *
    ∏i,L i^(2*d i)/((2*Real.pi^2)^(d i)*(2*d i+1).factorial)

def tightParameterScale (Y:ℝ) : ℝ := Real.sqrt (2*r Y)/Real.pi
lemma tightParameterScale_pos (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀) : 0<tightParameterScale Y :=
  div_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) (r_pos Y hY))) Real.pi_pos
lemma tightParameterScale_square (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀) :
    (tightParameterScale Y)^2/4=r Y/(2*Real.pi^2) := by
  unfold tightParameterScale
  rw [div_pow,Real.sq_sqrt (mul_nonneg (by norm_num) (r_pos Y hY).le)]
  ring
lemma tight_scaled_length_coefficient (Y L:ℝ) (hY:Y∈Ico (0:ℝ) y₀) (d:ℕ) :
    boundaryLengthCoefficient (tightParameterScale Y*L) d=
      r Y^d*(L^(2*d)/((2*Real.pi^2)^d*(2*d+1).factorial)) := by
  unfold boundaryLengthCoefficient
  rw [mul_pow,pow_mul,show (2*d:ℕ)=d*2 by omega,pow_mul]
  have hs:=tightParameterScale_square Y hY
  have hpow : tightParameterScale Y^2 = 4*(r Y/(2*Real.pi^2)) := by linarith
  rw [hpow,mul_pow]
  have h4:(4:ℝ)^d≠0:=by positivity
  rw [div_pow]
  field_simp
  <;> ring

lemma shifted_div_zero_eq_profile_mul_r (P:PsiTheory) (g:ℕ) (d:List ℕ)
    (hs:Stable g d.length) (hd:d.sum≤dimension g d.length)
    (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀) :
    shifted P g d Y/shifted P g (List.replicate d.length 0) Y =
      profile P g d Y*r Y^d.sum := by
  have ha:(a Y)^(complexity g d.length)≠0:=pow_ne_zero _ (a_pos Y hY).ne'
  have hr:(r Y)^(dimension g d.length-d.sum)≠0:=pow_ne_zero _ (r_pos Y hY).ne'
  have hpw:r Y^(dimension g d.length)=r Y^(dimension g d.length-d.sum)*r Y^d.sum := by
    rw [←pow_add,Nat.sub_add_cancel hd]
  unfold profile normalized
  rw [ite_eq_right (ne_of_lt hY.2),ite_eq_right (ne_of_lt hY.2)]
  simp only [List.length_replicate,deficit,List.sum_replicate,nsmul_zero,Nat.sub_zero]
  rw [hpw]
  field_simp [ha,hr,pow_ne_zero _ (r_pos Y hY).ne']

lemma tightShiftedPolynomial_div_profile_sum (P:PsiTheory) (g p:ℕ)
    (hs:Stable g p) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀) (L:Fin p→ℝ) :
    tightShiftedPolynomial P g p Y L/shifted P g (List.replicate p 0) Y =
      ∑d∈degreeTuples g p,profile P g (List.ofFn d) Y*
        boundaryDegreeWeight p (fun i=>tightParameterScale Y*L i) d := by
  unfold tightShiftedPolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : (List.ofFn d).sum≤dimension g (List.ofFn d).length := by
    simpa only [List.sum_ofFn,List.length_ofFn] using (mem_degreeTuples_iff g p d).mp hd
  have hratio:=shifted_div_zero_eq_profile_mul_r P g (List.ofFn d)
    (by simpa only [List.length_ofFn] using hs) hdeg Y hY
  simp only [List.length_ofFn,List.sum_ofFn] at hratio
  rw [show shifted P g (List.ofFn d) Y*
      (∏i,L i^(2*d i)/((2*Real.pi^2)^(d i)*(2*d i+1).factorial)) /
        shifted P g (List.replicate p 0) Y =
      (shifted P g (List.ofFn d) Y/shifted P g (List.replicate p 0) Y)*
        ∏i,L i^(2*d i)/((2*Real.pi^2)^(d i)*(2*d i+1).factorial) by ring,hratio]
  change _ = _ * ∏ i, boundaryLengthCoefficient (tightParameterScale Y*L i) (d i)
  simp_rw [tight_scaled_length_coefficient Y _ hY]
  rw [Finset.prod_mul_distrib,←Finset.prod_pow_eq_pow_sum]
  ring

lemma profile_ofFn_zero_of_not_mem_degreeTuples_parameter (P:PsiTheory) (g p:ℕ)
    (Y:ℝ) (d:Fin p→ℕ) (hd:d∉degreeTuples g p) :
    profile P g (List.ofFn d) Y=0 := by
  have he : dimension g p < ∑ i,d i :=
    lt_of_not_ge (mt (mem_degreeTuples_iff g p d).mpr hd)
  unfold profile
  rw [normalized_excess P g (List.ofFn d) Y
    (by simpa only [List.length_ofFn,List.sum_ofFn] using he),zero_div]

lemma tightShiftedPolynomial_div_profile_tsum (P:PsiTheory) (g p:ℕ)
    (hs:Stable g p) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀) (L:Fin p→ℝ) :
    tightShiftedPolynomial P g p Y L/shifted P g (List.replicate p 0) Y =
      ∑'d:Fin p→ℕ,profile P g (List.ofFn d) Y*
        boundaryDegreeWeight p (fun i=>tightParameterScale Y*L i) d := by
  classical
  rw [tightShiftedPolynomial_div_profile_sum P g p hs Y hY]
  symm
  apply tsum_eq_sum
  intro d hd
  rw [profile_ofFn_zero_of_not_mem_degreeTuples_parameter P g p Y d hd,zero_mul]

lemma profile_parameter_bounds (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) (d:Fin p→ℕ) :
    0≤profile P g (List.ofFn d) Y ∧ profile P g (List.ofFn d) Y≤1 := by
  exact normalized_profile_bounds P g (List.ofFn d)
    (by simpa only [List.length_ofFn] using hs)
    (by simpa only [List.length_ofFn] using hp) Y hY

lemma tightShiftedPolynomial_bounds (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀) (L:Fin p→ℝ) :
    1≤tightShiftedPolynomial P g p Y L/shifted P g (List.replicate p 0) Y ∧
    tightShiftedPolynomial P g p Y L/shifted P g (List.replicate p 0) Y≤
      ∏i,boundaryFactor 0 (tightParameterScale Y*L i) := by
  classical
  let W:=boundaryDegreeWeight p (fun i=>tightParameterScale Y*L i)
  have hprof:=profile_parameter_bounds P g p hp hs Y ⟨hY.1,hY.2.le⟩
  have hn(d:Fin p→ℕ):0≤profile P g (List.ofFn d) Y*W d:=
    mul_nonneg (hprof d).1 (boundaryDegreeWeight_nonneg _ _ _)
  have hsumm:Summable (fun d:Fin p→ℕ=>profile P g (List.ofFn d) Y*W d):=by
    apply (boundaryDegreeWeight_summable p (fun i=>tightParameterScale Y*L i)).of_nonneg_of_le hn
    intro d
    exact mul_le_of_le_one_left (boundaryDegreeWeight_nonneg _ _ _) (hprof d).2
  rw [tightShiftedPolynomial_div_profile_tsum P g p hs Y hY]
  constructor
  · have hterm:=hsumm.le_tsum (0:Fin p→ℕ) (fun d _=>hn d)
    have hzero:List.ofFn (0:Fin p→ℕ)=List.replicate p 0:=by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp
    simpa only [hzero,profile_replicate_zero P g p hp hs Y ⟨hY.1,hY.2.le⟩,
      W,boundaryDegreeWeight,Pi.zero_apply,Nat.mul_zero,pow_zero,Nat.zero_add,
      Nat.factorial_one,Nat.cast_one,mul_one,div_one,Finset.prod_const_one] using hterm
  · rw [←boundaryDegreeWeight_tsum]
    apply hsumm.tsum_le_tsum _ (boundaryDegreeWeight_summable p _)
    intro d
    exact mul_le_of_le_one_left (boundaryDegreeWeight_nonneg _ _ _) (hprof d).2

lemma degree_quadratic_le_four_pow (q:ℕ) : (q:ℝ)*(q+1)≤(4:ℝ)^q := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    by_cases hq:q=0
    · subst q; norm_num
    · have hq1:(1:ℝ)≤q:=by exact_mod_cast (show 1≤q by omega)
      have hpos:0≤((3:ℝ)*q-2)*(q+1):=mul_nonneg (by linarith) (by positivity)
      rw [pow_succ,Nat.cast_succ]
      nlinarith

lemma boundaryDegreeWeight_double (p:ℕ) (L:Fin p→ℝ) (d:Fin p→ℕ) :
    (4:ℝ)^(∑i,d i)*boundaryDegreeWeight p L d=
      boundaryDegreeWeight p (fun i=>2*L i) d := by
  unfold boundaryDegreeWeight
  simp_rw [mul_pow,pow_mul]
  norm_num only [show (2:ℝ)^2=4 by norm_num]
  rw [←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  ring

def tightProfileLoss (P:PsiTheory) (g p:ℕ) (Y:ℝ) (U:Fin p→ℝ) (d:Fin p→ℕ):ℝ:=
  (1-profile P g (List.ofFn d) Y)*boundaryDegreeWeight p U d

lemma tightProfileLoss_summable (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) (U:Fin p→ℝ) :
    Summable (tightProfileLoss P g p Y U) := by
  have hprof:=profile_parameter_bounds P g p hp hs Y hY
  apply (boundaryDegreeWeight_summable p U).of_nonneg_of_le
  · intro d
    exact mul_nonneg (by linarith [(hprof d).2]) (boundaryDegreeWeight_nonneg _ _ _)
  · intro d
    exact mul_le_of_le_one_left (boundaryDegreeWeight_nonneg _ _ _) (by linarith [(hprof d).1])

lemma tightProfileLoss_tsum_eq (P:PsiTheory) (g p:ℕ) (hp:1≤p) (hs:Stable g p)
    (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀) (L:Fin p→ℝ) :
    (∑'d:Fin p→ℕ,tightProfileLoss P g p Y (fun i=>tightParameterScale Y*L i) d)=
      (∏i,boundaryFactor 0 (tightParameterScale Y*L i))-
      tightShiftedPolynomial P g p Y L/shifted P g (List.replicate p 0) Y := by
  let U:=fun i=>tightParameterScale Y*L i
  have hprof:=profile_parameter_bounds P g p hp hs Y ⟨hY.1,hY.2.le⟩
  have hpS:Summable (fun d:Fin p→ℕ=>profile P g (List.ofFn d) Y*boundaryDegreeWeight p U d):=by
    apply (boundaryDegreeWeight_summable p U).of_nonneg_of_le
    · intro d
      exact mul_nonneg (hprof d).1 (boundaryDegreeWeight_nonneg _ _ _)
    · intro d
      exact mul_le_of_le_one_left (boundaryDegreeWeight_nonneg _ _ _) (hprof d).2
  rw [tightShiftedPolynomial_div_profile_tsum P g p hs Y hY,
    ←boundaryDegreeWeight_tsum,←(boundaryDegreeWeight_summable p U).tsum_sub hpS]
  apply tsum_congr
  intro d
  unfold tightProfileLoss U
  ring

lemma tightShiftedPolynomial_uniform_error (P:PsiTheory) (p:ℕ) (hp:1≤p) (B:ℝ) (hB:0≤B) :
    ∃ C:ℝ,0<C ∧ ∀ g:ℕ,1≤g→∀ Y∈Ico (0:ℝ) y₀,∀ L:Fin p→ℝ,
      (∀i,0≤L i)→(∀i,tightParameterScale Y*L i≤B)→
      |tightShiftedPolynomial P g p Y L/shifted P g (List.replicate p 0) Y-
        ∏i,boundaryFactor 0 (tightParameterScale Y*L i)|≤C/(g:ℝ) := by
  obtain ⟨C,hC,hbound⟩:=quadratic_profile_all_markings_proof P p hp
  let K:ℝ:=∏i:Fin p,boundaryFactor 0 (2*B)
  have hK:1≤K:=Finset.one_le_prod₀ (fun i _=>one_le_boundaryFactor 0 (2*B))
  refine ⟨C*K,mul_pos hC (by linarith),?_⟩
  intro g hg Y hY L hL hLU
  have hs:Stable g p:=by unfold Stable;omega
  have hgR:(0:ℝ)<g:=by exact_mod_cast (show 0<g by omega)
  let U:=fun i=>tightParameterScale Y*L i
  have hU:∀i,0≤U i:=fun i=>mul_nonneg (tightParameterScale_pos Y hY).le (hL i)
  have hprof:=profile_parameter_bounds P g p hp hs Y ⟨hY.1,hY.2.le⟩
  have hpoint(d:Fin p→ℕ):tightProfileLoss P g p Y U d≤
      (C/(g:ℝ))*boundaryDegreeWeight p (fun _=>2*B) d := by
    have hq:=hbound g hg (List.ofFn d) (by simp only [List.length_ofFn]) Y ⟨hY.1,hY.2.le⟩
    have hdeg:=degree_quadratic_le_four_pow (List.ofFn d).sum
    calc
      _ ≤ (C*(List.ofFn d).sum*((List.ofFn d).sum+1)/(g:ℝ))*boundaryDegreeWeight p U d :=
        mul_le_mul_of_nonneg_right hq.2 (boundaryDegreeWeight_nonneg _ _ _)
      _ = (C/(g:ℝ))*((List.ofFn d).sum*((List.ofFn d).sum+1))*boundaryDegreeWeight p U d := by ring
      _ ≤ (C/(g:ℝ))*(4:ℝ)^((List.ofFn d).sum)*boundaryDegreeWeight p U d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdeg (by positivity)) (boundaryDegreeWeight_nonneg _ _ _)
      _ = (C/(g:ℝ))*boundaryDegreeWeight p (fun i=>2*U i) d := by
        rw [mul_assoc,List.sum_ofFn,boundaryDegreeWeight_double]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (boundaryDegreeWeight_mono p (fun i=>2*U i) (fun _=>2*B)
          (fun i=>mul_nonneg (by norm_num) (hU i)) (fun i=>by dsimp [U];linarith [hLU i]) d) (by positivity)
  have hnon:0≤∑'d:Fin p→ℕ,tightProfileLoss P g p Y U d:=by
    apply tsum_nonneg
    intro d
    exact mul_nonneg (by linarith [(hprof d).2]) (boundaryDegreeWeight_nonneg _ _ _)
  rw [abs_sub_comm,←tightProfileLoss_tsum_eq P g p hp hs Y hY,abs_of_nonneg hnon]
  calc
    _ ≤ ∑'d:Fin p→ℕ,(C/(g:ℝ))*boundaryDegreeWeight p (fun _=>2*B) d :=
      (tightProfileLoss_summable P g p hp hs Y ⟨hY.1,hY.2.le⟩ U).tsum_le_tsum hpoint
        ((boundaryDegreeWeight_summable p (fun _=>2*B)).mul_left _)
    _ = C*K/(g:ℝ) := by rw [tsum_mul_left,boundaryDegreeWeight_tsum];dsimp [K];ring


lemma tightShiftedPolynomial_uniform_relative_error (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (B:ℝ) (hB:0≤B) :
    ∃ C:ℝ,0<C ∧ ∀ g:ℕ,1≤g→∀ Y∈Ico (0:ℝ) y₀,∀ L:Fin p→ℝ,
      (∀i,0≤L i)→(∀i,tightParameterScale Y*L i≤B)→
      |tightShiftedPolynomial P g p Y L/
        (shifted P g (List.replicate p 0) Y*
          ∏i,boundaryFactor 0 (tightParameterScale Y*L i))-1|≤C/(g:ℝ) := by
  obtain ⟨C,hC,hbound⟩:=tightShiftedPolynomial_uniform_error P p hp B hB
  refine ⟨C,hC,?_⟩
  intro g hg Y hY L hL hLU
  have hprod:1≤∏i,boundaryFactor 0 (tightParameterScale Y*L i):=
    Finset.one_le_prod₀ (fun i _=>one_le_boundaryFactor 0 _)
  have hpos:0<∏i,boundaryFactor 0 (tightParameterScale Y*L i):=by linarith
  rw [div_mul_eq_div_div,div_sub_one hpos.ne',abs_div,abs_of_pos hpos]
  exact (div_le_self (abs_nonneg _) hprod).trans (hbound g hg Y hY L hL hLU)

end WP
