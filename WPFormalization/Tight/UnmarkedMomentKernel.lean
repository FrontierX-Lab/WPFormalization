import WPFormalization.Analysis.KKernelPositivity
import WPFormalization.Volumes.PlanarInverse

/-! Ordinary raw-derivative moment logarithms for the unmarked tight factor.

All identities and positivity statements in this module are proved locally.
The moment series has coefficient X^(j+1), with no Taylor factorial.
-/
noncomputable section
namespace WP.Analysis.UnmarkedMoments
open Filter
open scoped Topology

def momentSeries (Y : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun j => iteratedDeriv (j+1) X Y)
@[simp] lemma momentSeries_coeff (Y : ℂ) (j : ℕ) :
    PowerSeries.coeff j (momentSeries Y)=iteratedDeriv (j+1) X Y := by
  simp [momentSeries]
@[simp] lemma momentSeries_constant (Y : ℂ) :
    PowerSeries.constantCoeff (momentSeries Y)=deriv X Y := by
  simp [momentSeries,iteratedDeriv_one]
lemma momentSeries_analyticAt (j : ℕ) (Y : ℂ) :
    AnalyticAt ℂ (fun W=>PowerSeries.coeff j (momentSeries W)) Y := by
  simp only [momentSeries_coeff]
  exact (iteratedDeriv_X_differentiable (j+1)).analyticAt Y
lemma inverseSeries_analyticAt (j : ℕ) (Y : ℂ) (ha : deriv X Y≠0) :
    AnalyticAt ℂ (fun W=>PowerSeries.coeff j ((momentSeries W)⁻¹)) Y := by
  have hc : AnalyticAt ℂ (fun W=>PowerSeries.constantCoeff (momentSeries W)) Y := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using momentSeries_analyticAt 0 Y
  have hci:=hc.inv (by simpa using ha)
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj:j=0
    · subst j
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv,
        Pi.inv_def] using hci
    · have he : (fun W=>PowerSeries.coeff j ((momentSeries W)⁻¹))=
          fun W=> -(PowerSeries.constantCoeff (momentSeries W))⁻¹*
            ∑i∈Finset.HasAntidiagonal.antidiagonal j,if i.2<j then
              PowerSeries.coeff i.1 (momentSeries W)*PowerSeries.coeff i.2 ((momentSeries W)⁻¹)
            else 0 := by
        funext W
        rw [PowerSeries.coeff_inv,ite_eq_right hj]
      rw [he]
      apply hci.neg.mul
      apply Finset.analyticAt_fun_sum
      intro i hi
      by_cases hlt:i.2<j
      · simp only [ite_eq_left hlt]
        exact (momentSeries_analyticAt i.1 Y).mul (ih i.2 hlt)
      · simp only [ite_eq_right hlt]
        exact analyticAt_const

def inverseCoeff (j : ℕ) (Y : ℂ) : ℂ :=
  deriv X Y*PowerSeries.coeff j ((momentSeries Y)⁻¹)
def logarithmicCoeff (j : ℕ) (Y : ℂ) : ℂ :=
  if j=0 then 0 else
    -PowerSeries.coeff (j-1) (PowerSeries.derivative (momentSeries Y)*(momentSeries Y)⁻¹)/(j:ℂ)
def logarithmicSeries (Y : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun j=>logarithmicCoeff j Y)
@[simp] lemma logarithmicCoeff_zero (Y : ℂ) : logarithmicCoeff 0 Y=0 := by
  simp [logarithmicCoeff]
@[simp] lemma logarithmicSeries_coeff (j : ℕ) (Y : ℂ) :
    PowerSeries.coeff j (logarithmicSeries Y)=logarithmicCoeff j Y := by
  simp [logarithmicSeries]
@[simp] lemma logarithmicSeries_constant (Y : ℂ) :
    PowerSeries.constantCoeff (logarithmicSeries Y)=0 := by
  simp [logarithmicSeries]
lemma logarithmicSeries_derivative (Y : ℂ) :
    PowerSeries.derivative (logarithmicSeries Y)=
      -PowerSeries.derivative (momentSeries Y)*(momentSeries Y)⁻¹ := by
  ext j
  simp only [PowerSeries.coeff_derivative,logarithmicSeries_coeff,logarithmicCoeff,
    Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel_right,map_neg,neg_mul]
  have hj : (j+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero j
  simp only [Nat.cast_add,Nat.cast_one]
  exact div_mul_cancel₀ _ (by simpa using hj)
lemma logarithmicSeries_identity (Y : ℂ) (ha : deriv X Y≠0) :
    PowerSeries.derivative (logarithmicSeries Y)*momentSeries Y=
      -PowerSeries.derivative (momentSeries Y) := by
  rw [logarithmicSeries_derivative,mul_assoc,PowerSeries.inv_mul_cancel _ (by simpa using ha),mul_one]
lemma inverseCoeff_zero (Y : ℂ) (ha : deriv X Y≠0) : inverseCoeff 0 Y=1 := by
  simp [inverseCoeff,ha]
lemma inverseCoeff_analyticAt (j : ℕ) (Y : ℂ) (ha : deriv X Y≠0) :
    AnalyticAt ℂ (inverseCoeff j) Y :=
  ((X_differentiable.analyticAt Y).deriv).mul (inverseSeries_analyticAt j Y ha)
lemma logarithmicCoeff_analyticAt (j : ℕ) (Y : ℂ) (ha : deriv X Y≠0) :
    AnalyticAt ℂ (logarithmicCoeff j) Y := by
  unfold logarithmicCoeff
  split_ifs with hj
  · exact analyticAt_const
  · apply AnalyticAt.div_const
    apply AnalyticAt.neg
    simp only [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.analyticAt_fun_sum
    intro i hi
    simp only [PowerSeries.coeff_derivative]
    exact ((momentSeries_analyticAt (i+1) Y).mul analyticAt_const).mul
      (inverseSeries_analyticAt (j-1-i) Y ha)
lemma momentSeries_parameter (Y : ℂ) :
    coefficientDeriv momentSeries Y=shiftSeries (momentSeries Y) := by
  ext j
  simp only [coefficientDeriv_coeff,momentSeries_coeff,shiftSeries_coeff]
  rw [←iteratedDeriv_succ]
lemma logarithmicSeries_parameter (Y : ℂ) (ha : deriv X Y≠0) :
    coefficientDeriv logarithmicSeries Y=
      PowerSeries.C (deriv (deriv X) Y/deriv X Y)+
        shiftSeries (PowerSeries.C (deriv X Y)*(momentSeries Y)⁻¹) := by
  have hane : ∀ᶠ W in 𝓝 Y, deriv X W≠0 :=
    ((X_differentiable.analyticAt Y).deriv).continuousAt.eventually_ne ha
  have hp:=coefficientDeriv_log_ratio momentSeries logarithmicSeries Y
    (fun j=>momentSeries_analyticAt j Y) (fun j=>by simpa only [logarithmicSeries_coeff] using logarithmicCoeff_analyticAt j Y ha)
    (by simpa using ha)
    (hane.mono (fun W hW=>logarithmicSeries_identity W hW))
    (Filter.Eventually.of_forall logarithmicSeries_constant)
  rw [momentSeries_parameter,shiftSeries_mul_inv _ (by simpa using ha)] at hp
  simpa only [momentSeries_constant,sub_neg_eq_add,shiftSeries_coeff,momentSeries_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,←PowerSeries.coeff_zero_eq_constantCoeff,
    shiftSeries_coeff,momentSeries_coeff,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hp
lemma logarithmicCoeff_parameter (j : ℕ) (hj : 0<j) (Y : ℂ) (ha : deriv X Y≠0) :
    deriv (logarithmicCoeff j) Y=inverseCoeff (j+1) Y := by
  have h:=congrArg (PowerSeries.coeff j) (logarithmicSeries_parameter Y ha)
  simpa only [coefficientDeriv_coeff,logarithmicSeries_coeff,map_add,
    PowerSeries.coeff_C,ite_eq_right (ne_of_gt hj),zero_add,shiftSeries_coeff,
    PowerSeries.coeff_C_mul,inverseCoeff] using h
lemma inverseSeries_differential (Y : ℂ) :
    PowerSeries.derivative (PowerSeries.C (deriv X Y)*(momentSeries Y)⁻¹)=
      PowerSeries.derivative (logarithmicSeries Y)*
        (PowerSeries.C (deriv X Y)*(momentSeries Y)⁻¹) := by
  rw [Derivation.leibniz,PowerSeries.derivative_C,smul_zero,add_zero,
    PowerSeries.derivative_inv',logarithmicSeries_derivative]
  simp only [smul_eq_mul]
  ring
lemma normalizedInverseSeries_coeff (j : ℕ) (Y : ℂ) :
    PowerSeries.coeff j (PowerSeries.C (deriv X Y)*(momentSeries Y)⁻¹)=inverseCoeff j Y := by
  rw [PowerSeries.coeff_C_mul]
  rfl
lemma inverseCoeff_recursion (j : ℕ) (Y : ℂ) :
    (j+1:ℂ)*inverseCoeff (j+1) Y=
      ∑ i ∈ Finset.range (j+1), (i+1:ℂ)*logarithmicCoeff (i+1) Y*inverseCoeff (j-i) Y := by
  have h:=congrArg (PowerSeries.coeff j) (inverseSeries_differential Y)
  rw [PowerSeries.coeff_derivative,normalizedInverseSeries_coeff] at h
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [PowerSeries.coeff_derivative,logarithmicSeries_coeff,normalizedInverseSeries_coeff] at h
  change inverseCoeff (j+1) Y*(j+1:ℂ)=
    ∑ i ∈ Finset.range (j+1), (logarithmicCoeff (i+1) Y*(i+1:ℂ))*inverseCoeff (j-i) Y at h
  calc
    _=inverseCoeff (j+1) Y*(j+1:ℂ) := by ring
    _=_ := h
    _=_ := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
lemma momentSeries_initial_differential :
    PowerSeries.derivative (momentSeries 0)= -momentSeries 0 := by
  ext j
  simp only [PowerSeries.coeff_derivative,momentSeries_coeff,map_neg,
    iteratedDeriv_X_succ_zero,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  have hj:(j.factorial:ℂ)≠0 := by exact_mod_cast j.factorial_ne_zero
  have hn:(j+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero j
  field_simp
lemma logarithmicSeries_initial : logarithmicSeries 0=PowerSeries.X := by
  have ha:deriv X (0:ℂ)≠0 := by rw [derivX_zero];exact one_ne_zero
  apply PowerSeries.derivative.ext
  · rw [logarithmicSeries_derivative,momentSeries_initial_differential,neg_neg,
      PowerSeries.mul_inv_cancel _ (by simpa using ha),PowerSeries.derivative_X]
  · simp
lemma logarithmicCoeff_initial (j : ℕ) :
    logarithmicCoeff j 0=if j=1 then 1 else 0 := by
  have h:=congrArg (PowerSeries.coeff j) logarithmicSeries_initial
  simpa only [logarithmicSeries_coeff,PowerSeries.coeff_X] using h
lemma inverseSeries_parameter_real (j : ℕ) :
    RealCoefficients (fun W=>PowerSeries.coeff j ((momentSeries W)⁻¹)) := by
  have ha:deriv X (0:ℂ)≠0 := by rw [derivX_zero];exact one_ne_zero
  have hci:RealCoefficients (fun W=>(PowerSeries.constantCoeff (momentSeries W))⁻¹) := by
    apply realCoefficients_inv
    · simpa only [momentSeries_constant] using (X_differentiable.analyticAt (0:ℂ)).deriv
    · simpa using ha
    · simpa only [momentSeries_constant,iteratedDeriv_one] using realCoefficients_iteratedDeriv_X 1
  have hcA:AnalyticAt ℂ (fun W=>PowerSeries.constantCoeff (momentSeries W)) 0 := by
    simpa only [momentSeries_constant] using (X_differentiable.analyticAt (0:ℂ)).deriv
  have hciA:=hcA.inv (by simpa using ha)
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj:j=0
    · subst j
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv] using hci
    · let A (i : ℕ×ℕ) (W : ℂ) : ℂ :=
        if i.2<j then PowerSeries.coeff i.1 (momentSeries W)*
          PowerSeries.coeff i.2 ((momentSeries W)⁻¹) else 0
      have hA (i : ℕ×ℕ) : AnalyticAt ℂ (A i) 0 := by
        dsimp [A]
        split_ifs with hlt
        · exact (momentSeries_analyticAt i.1 0).mul (inverseSeries_analyticAt i.2 0 ha)
        · exact analyticAt_const
      have hR (i : ℕ×ℕ) : RealCoefficients (A i) := by
        dsimp [A]
        split_ifs with hlt
        · apply realCoefficients_mul (momentSeries_analyticAt i.1 0)
            (inverseSeries_analyticAt i.2 0 ha)
          · simpa only [momentSeries_coeff] using realCoefficients_iteratedDeriv_X (i.1+1)
          · exact ih i.2 hlt
        · exact realCoefficients_real_const 0
      have hsA:=Finset.analyticAt_fun_sum (Finset.HasAntidiagonal.antidiagonal j)
        (fun i hi=>hA i)
      have hsR:=realCoefficients_finset_sum (Finset.HasAntidiagonal.antidiagonal j) A
        (fun i hi=>hA i) (fun i hi=>hR i)
      have hmul:=realCoefficients_mul hciA hsA hci hsR
      have hneg:=realCoefficients_const_mul (-1) hmul
      have he:(fun W=>PowerSeries.coeff j ((momentSeries W)⁻¹))=
          fun W=> (-1:ℂ)*((PowerSeries.constantCoeff (momentSeries W))⁻¹*
            ∑i∈Finset.HasAntidiagonal.antidiagonal j,A i W) := by
        funext W
        rw [PowerSeries.coeff_inv,ite_eq_right hj]
        dsimp [A]
        ring
      rw [he]
      simpa only [Complex.ofReal_neg,Complex.ofReal_one,Pi.inv_def] using hneg
lemma inverseCoeff_parameter_real (j : ℕ) : RealCoefficients (inverseCoeff j) := by
  have ha:deriv X (0:ℂ)≠0 := by rw [derivX_zero];exact one_ne_zero
  exact realCoefficients_mul (X_differentiable.analyticAt (0:ℂ)).deriv
    (inverseSeries_analyticAt j 0 ha)
    (by simpa only [iteratedDeriv_one] using realCoefficients_iteratedDeriv_X 1)
    (inverseSeries_parameter_real j)
lemma logarithmicCoeff_parameter_real (j : ℕ) : RealCoefficients (logarithmicCoeff j) := by
  have ha:deriv X (0:ℂ)≠0 := by rw [derivX_zero];exact one_ne_zero
  unfold logarithmicCoeff
  split_ifs with hj
  · exact realCoefficients_real_const 0
  · let A (i : ℕ) (W : ℂ) : ℂ :=
      (PowerSeries.coeff (i+1) (momentSeries W)*(i+1:ℂ))*
        PowerSeries.coeff (j-1-i) ((momentSeries W)⁻¹)
    have hA(i:ℕ):AnalyticAt ℂ (A i) 0 :=
      ((momentSeries_analyticAt (i+1) 0).mul analyticAt_const).mul
        (inverseSeries_analyticAt (j-1-i) 0 ha)
    have hR(i:ℕ):RealCoefficients (A i) := by
      have hm:RealCoefficients (fun W=>PowerSeries.coeff (i+1) (momentSeries W)*(i+1:ℂ)) := by
        have hs:=realCoefficients_const_mul (i+1:ℝ)
          (realCoefficients_iteratedDeriv_X (i+1+1))
        apply realCoefficients_congr hs
        exact Filter.Eventually.of_forall (fun W=>by simp only [Complex.ofReal_add,
          Complex.ofReal_natCast,Complex.ofReal_one,momentSeries_coeff];ring)
      exact realCoefficients_mul ((momentSeries_analyticAt (i+1) 0).mul analyticAt_const)
        (inverseSeries_analyticAt (j-1-i) 0 ha) hm (inverseSeries_parameter_real _)
    have hsA:=Finset.analyticAt_fun_sum (Finset.range j) (fun i hi=>hA i)
    have hsR:=realCoefficients_finset_sum (Finset.range j) A
      (fun i hi=>hA i) (fun i hi=>hR i)
    have hnA:=hsA.neg
    have hnR:=realCoefficients_const_mul (-1) hsR
    have hnR':RealCoefficients (fun W=>-(∑i∈Finset.range j,A i W)) := by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using hnR
    have hdR:=realCoefficients_div hnA analyticAt_const (by exact_mod_cast hj)
      hnR' (realCoefficients_real_const (j:ℝ))
    simp only [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      PowerSeries.coeff_derivative]
    simpa only [Nat.succ_eq_add_one,Nat.sub_add_cancel (by omega : 1≤j),
      Complex.ofReal_natCast,Pi.neg_apply,A] using hdR
lemma inverseCoeff_realTaylor_zero : realTaylor (inverseCoeff 0) = 1 := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have he : inverseCoeff 0 =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    exact inverseCoeff_zero Y hY
  apply realTaylor_of_taylor_map
  rw [taylor_congr he,taylor_const]
  simp
lemma inverseCoeff_realTaylor_recursion (m : ℕ) :
    PowerSeries.C (m+1 : ℝ)*realTaylor (inverseCoeff (m+1)) =
      ∑ i ∈ Finset.range (m+1), PowerSeries.C (i+1 : ℝ)*
        (realTaylor (logarithmicCoeff (i+1))*realTaylor (inverseCoeff (m-i))) := by
  have ha : deriv X (0 : ℂ) ≠ 0 := by rw [derivX_zero]; exact one_ne_zero
  have he : (fun Y => Complex.ofReal (m+1 : ℝ)*inverseCoeff (m+1) Y) =ᶠ[𝓝 0]
      (fun Y => ∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*logarithmicCoeff (i+1) Y*inverseCoeff (m-i) Y) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    push_cast
    exact inverseCoeff_recursion m Y
  have ht := realTaylor_congr_event he
  rw [realTaylor_const_mul,realTaylor_finset_sum] at ht
  · calc
      _ = ∑ i ∈ Finset.range (m+1), realTaylor (fun Y => (i+1 : ℂ)*logarithmicCoeff (i+1) Y*inverseCoeff (m-i) Y) := ht
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfi : (fun Y => (i+1 : ℂ)*logarithmicCoeff (i+1) Y*inverseCoeff (m-i) Y) =
            fun Y => Complex.ofReal (i+1 : ℝ)*(logarithmicCoeff (i+1) Y*inverseCoeff (m-i) Y) := by
          funext Y
          push_cast
          ring
        rw [hfi,realTaylor_const_mul (i+1 : ℝ) (fun Y => logarithmicCoeff (i+1) Y*inverseCoeff (m-i) Y),
          realTaylor_mul (logarithmicCoeff_analyticAt (i+1) 0 ha) (inverseCoeff_analyticAt (m-i) 0 ha)
            (logarithmicCoeff_parameter_real (i+1)) (inverseCoeff_parameter_real (m-i))]
  · intro i hi
    exact (analyticAt_const.mul (logarithmicCoeff_analyticAt (i+1) 0 ha)).mul (inverseCoeff_analyticAt (m-i) 0 ha)
lemma zero_beta_parameter_nonnegative (t u : ℕ → PowerSeries ℝ)
    (ht0 : ∀m,0≤PowerSeries.coeff 0 (t (m+1)))
    (hu0 : u 0=1)
    (hu : ∀(m : ℕ),PowerSeries.C (m+1:ℝ)*u (m+1)=
      ∑i∈Finset.range (m+1),PowerSeries.C (i+1:ℝ)*(t (i+1)*u (m-i)))
    (ht : ∀m,PowerSeries.derivative (t (m+1))=u (m+2)) :
    (∀q m,0≤PowerSeries.coeff q (t (m+1))) ∧
      (∀q m,0≤PowerSeries.coeff q (u m)) := by
  have htall : ∀q m,0≤PowerSeries.coeff q (t (m+1)) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      cases q with
      | zero => exact ht0
      | succ q =>
        have hl : ∀m j,j≤q→0≤PowerSeries.coeff j (t (m+1)) :=
          fun m j hj=>ih j (by omega) m
        have hul:=inverse_log_coeff_nonneg t u q hu0 hu hl
        intro m
        have h:=congrArg (PowerSeries.coeff q) (ht m)
        simp only [PowerSeries.coeff_derivative] at h
        have hp : 0≤PowerSeries.coeff (q+1) (t (m+1))*(q+1:ℝ) :=
          h.symm ▸ hul (m+2) q le_rfl
        exact (mul_nonneg_iff_of_pos_right (by positivity : (0:ℝ)<q+1)).mp hp
  exact ⟨htall,fun q m=>inverse_log_coeff_nonneg t u q hu0 hu
    (fun m j hj=>htall j m) m q le_rfl⟩
lemma logarithmicCoeff_realTaylor_parameter (m : ℕ) :
    PowerSeries.derivative (realTaylor (logarithmicCoeff (m+1)))=
      realTaylor (inverseCoeff (m+2)) := by
  have ha:deriv X (0:ℂ)≠0 := by rw [derivX_zero];exact one_ne_zero
  have he:deriv (logarithmicCoeff (m+1))=ᶠ[𝓝 0] inverseCoeff (m+2) := by
    filter_upwards [((X_differentiable.analyticAt 0).deriv).continuousAt.eventually_ne ha] with Y hY
    exact logarithmicCoeff_parameter (m+1) (Nat.succ_pos m) Y hY
  have ht:=realTaylor_congr_event he
  rw [realTaylor_deriv] at ht
  exact ht
lemma ordinary_moment_parameter_nonnegative :
    (∀q m,0≤PowerSeries.coeff q (realTaylor (logarithmicCoeff (m+1)))) ∧
      (∀q m,0≤PowerSeries.coeff q (realTaylor (inverseCoeff m))) := by
  apply zero_beta_parameter_nonnegative (fun m=>realTaylor (logarithmicCoeff m))
    (fun m=>realTaylor (inverseCoeff m)) _ inverseCoeff_realTaylor_zero
    inverseCoeff_realTaylor_recursion logarithmicCoeff_realTaylor_parameter
  intro m
  simp only [realTaylor_coeff,realCoeff,WP.coeff,Nat.factorial_zero,Nat.cast_one,
    div_one,iteratedDeriv_zero,logarithmicCoeff_initial]
  split_ifs <;> norm_num
lemma logarithmicCoeff_realCoeff_nonnegative (m q : ℕ) (hm : 0 < m) :
    0≤realCoeff (logarithmicCoeff m) q := by
  cases m with
  | zero => omega
  | succ m => simpa only [realTaylor_coeff] using ordinary_moment_parameter_nonnegative.1 q m
lemma logarithmicCoeff_positiveJets (m : ℕ) (hm : 0 < m) :
    PositiveConvolution.PositiveJets (logarithmicCoeff m) := by
  apply PositiveConvolution.PositiveJets.of_coefficients
  · intro q
    exact logarithmicCoeff_realCoeff_nonnegative m q hm
  · exact logarithmicCoeff_parameter_real m
lemma logarithmicCoeff_hasSum (m : ℕ) (Y : ℂ) (hY : ‖Y‖<y₀) :
    HasSum (fun q=>WP.coeff (logarithmicCoeff m) q*Y^q) (logarithmicCoeff m Y) := by
  apply PositiveConvolution.analytic_ball_hasSum _ y₀ y₀_pos _ Y hY
  intro W hW
  exact logarithmicCoeff_analyticAt m W (derivX_ne_zero_of_norm_lt W hW)
lemma logarithmicCoeff_ofReal (m : ℕ) (Y : ℝ) (hY : Y∈Set.Ico (0:ℝ) y₀) :
    logarithmicCoeff m (Y:ℂ)=Complex.ofReal ((logarithmicCoeff m (Y:ℂ)).re) := by
  have hn:‖(Y:ℂ)‖<y₀ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hY.1] using hY.2
  have hs:=logarithmicCoeff_hasSum m (Y:ℂ) hn
  have hterm(q:ℕ):(WP.coeff (logarithmicCoeff m) q*(Y:ℂ)^q).im=0 := by
    rw [←Complex.ofReal_pow]
    simp only [Complex.mul_im,logarithmicCoeff_parameter_real m q,Complex.ofReal_im,
      mul_zero,zero_mul,add_zero]
  have hi:=Complex.imCLM.hasSum hs
  change HasSum (fun q=>(WP.coeff (logarithmicCoeff m) q*(Y:ℂ)^q).im)
    (logarithmicCoeff m (Y:ℂ)).im at hi
  have hz:HasSum (fun _:ℕ=>(0:ℝ)) (logarithmicCoeff m (Y:ℂ)).im := by
    simpa only [hterm] using hi
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using (hasSum_zero.unique hz).symm
lemma logarithmicCoeff_real_nonnegative (m : ℕ) (hm : 0 < m)
    (Y : ℝ) (hY : Y∈Set.Ico (0:ℝ) y₀) : 0≤(logarithmicCoeff m (Y:ℂ)).re := by
  have hn:‖(Y:ℂ)‖<y₀ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hY.1] using hY.2
  have hs:=Complex.reCLM.hasSum (logarithmicCoeff_hasSum m (Y:ℂ) hn)
  have ht(q:ℕ):0≤(WP.coeff (logarithmicCoeff m) q*(Y:ℂ)^q).re := by
    rw [←Complex.ofReal_pow,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonneg (logarithmicCoeff_realCoeff_nonnegative m q hm) (pow_nonneg hY.1 q)
  exact hs.nonneg ht

def physicalLogarithmicCoeff (P : PsiTheory) (m : ℕ) (z : ℂ) : ℂ :=
  logarithmicCoeff m (PositiveConvolution.planarInverse P z)
lemma physicalLogarithmicCoeff_analyticAt (P : PsiTheory) (m : ℕ) (z : ℂ)
    (hz : ‖z‖<xCritical) : AnalyticAt ℂ (physicalLogarithmicCoeff P m) z := by
  exact (logarithmicCoeff_analyticAt m _
    (PositiveConvolution.derivX_planarInverse_ne_zero P z hz)).comp
      (PositiveConvolution.planarInverse_analyticAt P z hz)
lemma physicalLogarithmicCoeff_positiveJets (P : PsiTheory) (m : ℕ) (hm : 0 < m) :
    PositiveConvolution.PositiveJets (physicalLogarithmicCoeff P m) := by
  have hz:‖(0:ℂ)‖<xCritical := by simpa only [norm_zero] using xCritical_pos_parameter
  have ha:deriv X (0:ℂ)≠0 := by rw [derivX_zero];exact one_ne_zero
  exact PositiveConvolution.PositiveJets.comp (f := logarithmicCoeff m)
    (g := PositiveConvolution.planarInverse P) (logarithmicCoeff_analyticAt m 0 ha)
    (PositiveConvolution.planarInverse_analyticAt P 0 hz)
    (PositiveConvolution.planarInverse_zero P) (logarithmicCoeff_positiveJets m hm)
    (PositiveConvolution.planarInverse_positiveJets P)
lemma momentSeries_reconstruction (Y : ℂ) (ha : deriv X Y≠0) :
    (PowerSeries.exp ℂ).subst (-logarithmicSeries Y)=
      PowerSeries.C ((deriv X Y)⁻¹)*momentSeries Y := by
  let E : PowerSeries ℂ := (PowerSeries.exp ℂ).subst (-logarithmicSeries Y)
  have ht:PowerSeries.HasSubst (-logarithmicSeries Y) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  have hE0:PowerSeries.constantCoeff E=1 := by
    dsimp [E]
    rw [PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero
        (by simp : PowerSeries.constantCoeff (-logarithmicSeries Y)=0)]
    simp
  have hED:PowerSeries.derivative E=E*(PowerSeries.derivative (momentSeries Y)*(momentSeries Y)⁻¹) := by
    dsimp [E]
    rw [PowerSeries.derivative_subst ht,PowerSeries.derivative_exp,map_neg,
      logarithmicSeries_derivative]
    ring
  have hD:PowerSeries.derivative (E*(momentSeries Y)⁻¹)=0 := by
    rw [Derivation.leibniz,PowerSeries.derivative_inv',hED]
    simp only [smul_eq_mul]
    ring
  have hC:PowerSeries.constantCoeff (E*(momentSeries Y)⁻¹)=(deriv X Y)⁻¹ := by
    simp [hE0]
  have hEq:E*(momentSeries Y)⁻¹=PowerSeries.C ((deriv X Y)⁻¹) := by
    apply PowerSeries.derivative.ext
    · rw [hD,PowerSeries.derivative_C]
    · simpa using hC
  have h:=congrArg (fun F : PowerSeries ℂ=>F*momentSeries Y) hEq
  rwa [mul_assoc,PowerSeries.inv_mul_cancel _ (by simpa using ha),mul_one] at h
end WP.Analysis.UnmarkedMoments
