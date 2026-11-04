import WPFormalization.Volumes.OriginStandardPhysical
import WPFormalization.Volumes.StrongOptimalModel
/-! Common growth of the same finite origin model on the standardized disk.
The already proved actual leading Gaussian chart is multiplied by the ratio
of the SAME finite canonical factors. Their common parameter-neighborhood
bounds give the ratio bound four. One joint shrink keeps every complex tilt
in the genuine source disk, independent of genus and retained order.
No coefficient family, order kappa or truncation J is reselected. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology

def centeredOriginFiniteModel (P:PsiTheory)(g p J:ℕ)(S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)
    (x:ℝ)(w:ℂ):ℂ:=
  let h:ℝ:=complexity g p
  let σ:ℝ:=Real.sqrt (h*euler Psi x)
  Complex.exp (-(h:ℂ)*(Psi x:ℂ)*(w/(σ:ℂ)))*
    (normalizedFiniteMarkedModel P g p S Bc L J ((x:ℂ)*Complex.exp (w/(σ:ℂ)))/
      normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ))

lemma centeredOriginFiniteModel_factorization (P:PsiTheory)(g p J:ℕ)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(x:ℝ)(w:ℂ):
    let h:ℝ:=complexity g p
    let σ:ℝ:=Real.sqrt (h*euler Psi x)
    let z:ℂ:=(x:ℂ)*Complex.exp (w/(σ:ℂ))
    centeredOriginFiniteModel P g p J S Bc L x w=
      (Complex.exp (-(h:ℂ)*(Psi x:ℂ)*(w/(σ:ℂ)))*
        ((Complex.exp ((h:ℂ)*S z)*Bc z)/(Complex.exp ((h:ℂ)*S (x:ℂ))*Bc (x:ℂ))))*
        (finiteMarkedFactor L h J (PositiveConvolution.planarInverse P z)/
          finiteMarkedFactor L h J (PositiveConvolution.planarInverse P (x:ℂ))):=by
  dsimp only
  unfold centeredOriginFiniteModel normalizedFiniteMarkedModel
  simp only[Complex.ofReal_natCast,div_eq_mul_inv,mul_inv_rev]
  ring

lemma origin_finite_model_growth_of_source (P:PsiTheory)(p:ℕ)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(S Bc:ℂ→ℂ)(ρs:ℝ)
    (hρs:0<ρs)(hρsx:ρs<xCritical)
    (hS:AnalyticAt ℂ S 0)(hSd:deriv S 0=2)(hBc:AnalyticAt ℂ Bc 0)(hBc0:Bc 0≠0)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ))
    (hBr:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ))
    (hmap:∀z:ℂ,‖z‖≤ρs→PositiveConvolution.planarInverse P z∈Ω):
    ∃η ρ C D K:ℝ,0<η ∧ η<ρs ∧ 0<ρ ∧ 0<C ∧ 0<D ∧ 0<K ∧
      (∀x∈Ioo (0:ℝ) η,1≤deriv Psi x ∧ Psi x≤K*x) ∧
      ∀g J:ℕ,0<(complexity g p:ℝ)→
      (∀z∈Ω,1/2≤‖finiteMarkedFactor L (complexity g p:ℝ) J z‖ ∧
        ‖finiteMarkedFactor L (complexity g p:ℝ) J z‖≤2)→
      (∀z:ℂ,‖z‖≤ρs→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z)→
      ∀x∈Ioo (0:ℝ) η,
        AnalyticOnNhd ℂ (centeredOriginFiniteModel P g p J S Bc L x)
          (Metric.ball 0 (ρ*Real.sqrt ((complexity g p:ℝ)*x))) ∧
        ∀w:ℂ,‖w‖≤ρ*Real.sqrt ((complexity g p:ℝ)*x)→
          ‖centeredOriginFiniteModel P g p J S Bc L x w‖≤D*Real.exp (C*‖w‖^2) ∧
            ‖(x:ℂ)*Complex.exp (w/(Real.sqrt ((complexity g p:ℝ)*euler Psi x):ℂ))‖≤ρs:=by
  obtain ⟨G,Amp,η0,ρ0,C,D0,K,hη0,hη0x,hρ0,hC,hD0,hK,hmean,hstd,hphysical⟩:=
    Analysis.origin_standard_gaussian_physical_data p S Bc hS hSd hBc hBc0 hSr hBr
  let η:ℝ:=min η0 (ρs/(2*Real.exp 1))
  let ρ:ℝ:=min ρ0 1
  have hη:0<η:=lt_min hη0 (by positivity)
  have hη0':η≤η0:=min_le_left _ _
  have hηs:η<ρs:=by
    have he:1≤Real.exp (1:ℝ):=Real.one_le_exp (by norm_num)
    have hd:1<2*Real.exp (1:ℝ):=by linarith
    have hr:ρs/(2*Real.exp 1)<ρs:=(div_lt_self hρs hd)
    exact (min_le_right _ _).trans_lt hr
  have hρ:0<ρ:=lt_min hρ0 zero_lt_one
  have hρ0':ρ≤ρ0:=min_le_left _ _
  have hρ1:ρ≤1:=min_le_right _ _
  refine ⟨η,ρ,C,4*D0,K,hη,hηs,hρ,hC,by positivity,hK,?_,?_⟩
  · intro x hx
    exact hmean x ⟨hx.1,hx.2.trans_le hη0'⟩
  · intro g J hh hP hMa x hx
    let h:ℝ:=complexity g p
    let σ:ℝ:=Real.sqrt (h*euler Psi x)
    let Z:ℂ→ℂ:=fun w=>(x:ℂ)*Complex.exp (w/(σ:ℂ))
    have hxh:x∈Ioo (0:ℝ) η0:=⟨hx.1,hx.2.trans_le hη0'⟩
    have hder:1≤deriv Psi x:=(hmean x hxh).1
    have hnbase:‖(x:ℂ)‖≤ρs:=by rw[Complex.norm_of_nonneg hx.1.le];exact hx.2.le.trans hηs.le
    have hbase:1/2≤‖finiteMarkedFactor L h J (PositiveConvolution.planarInverse P (x:ℂ))‖:=
      (hP _ (hmap _ hnbase)).1
    have hz(w:ℂ)(hw:‖w‖≤ρ*Real.sqrt (h*x)):‖Z w‖≤ρs:=by
      have ht:=Analysis.origin_complex_tilt_norm h x ρ w hh hx.1 hρ.le hder hw
      have he:Real.exp ρ≤Real.exp (1:ℝ):=Real.exp_le_exp.mpr hρ1
      have hsmall:x*Real.exp (1:ℝ)<ρs/2:=by
        have ht:x<ρs/(2*Real.exp 1):=hx.2.trans_le (min_le_right _ _)
        have hh':= (lt_div_iff₀ (by positivity:0<2*Real.exp 1)).mp ht
        nlinarith
      exact ht.trans ((mul_le_mul_of_nonneg_left he hx.1.le).trans (by linarith))
    have hstdx:=hstd h x hh hxh
    refine ⟨?_,?_⟩
    · intro w hw
      have hn:‖w‖≤ρ*Real.sqrt (h*x):=(by simpa only[Metric.mem_ball,dist_zero_right] using hw : ‖w‖<ρ*Real.sqrt (h*x)).le
      have ha:AnalyticAt ℂ (fun w:ℂ=>normalizedFiniteMarkedModel P g p S Bc L J (Z w)) w:=
        AnalyticAt.comp (f:=Z) (x:=w) (hMa _ (hz w hn)) (by dsimp[Z];fun_prop)
      unfold centeredOriginFiniteModel
      exact (by fun_prop:AnalyticAt ℂ (fun v:ℂ=>Complex.exp (-(h:ℂ)*(Psi x:ℂ)*(v/(σ:ℂ)))) w).mul ha.div_const
    · intro w hw
      refine ⟨?_,hz w hw⟩
      have hs:=hstdx.2.2.2.2.2.2 w (hw.trans (mul_le_mul_of_nonneg_right hρ0' (Real.sqrt_nonneg (h*x))))
      have hnum:‖finiteMarkedFactor L h J (PositiveConvolution.planarInverse P (Z w))‖≤2:=
        (hP _ (hmap _ (hz w hw))).2
      have hratio:‖finiteMarkedFactor L h J (PositiveConvolution.planarInverse P (Z w))/
          finiteMarkedFactor L h J (PositiveConvolution.planarInverse P (x:ℂ))‖≤4:=by
        rw[norm_div]
        apply (div_le_iff₀ (by linarith:0<‖finiteMarkedFactor L h J (PositiveConvolution.planarInverse P (x:ℂ))‖)).mpr
        linarith
      rw[centeredOriginFiniteModel_factorization]
      rw[hs.2.2,norm_mul,norm_mul]
      have hex:‖Complex.exp (Analysis.originStandardLog G h x w)‖≤Real.exp (C*‖w‖^2):=
        (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hs.1)
      have ht:=mul_le_mul (mul_le_mul hex hs.2.1 (norm_nonneg _) (Real.exp_pos _).le)
        hratio (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hD0.le)
      nlinarith
end WP.HigherOrder
