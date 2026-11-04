import WPFormalization.HigherOrder.ComplexInverseCuspBounds
import WPFormalization.Analysis.UniformDslopeBound
import WPFormalization.HigherOrder.FixedMarkingGevreyScale
import WPFormalization.HigherOrder.RecursiveRemainderProof
/-! All canonical transport quotients have a genuine uniform norm on one common complex neighborhood. Actual critical vanishing, one Cauchy ball and compact nonzero denominator control remove the simple root simultaneously at every order. -/
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open Set PowerSeries Filter
open scoped Topology
lemma common_transport_quotient_order_bounds (P:PsiTheory) :
    ∃(V:Set ℂ)(C B:ℝ)(M:ℕ),IsOpen V ∧ Convex ℝ V ∧
      (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈V) ∧0<C ∧0<B ∧2 ≤ M ∧
      ∀p j:ℕ,1 ≤ p→1 ≤ j→∃F:ℂ→ℂ,AnalyticOnNhd ℂ F V ∧
        (∀Y∈Ico (0:ℝ) y₀,F (Y:ℂ)=((WP.HigherOrder.transportCoefficient P p j Y/(A Y*r Y):ℝ):ℂ)) ∧
        ∀z∈V,‖F z‖ ≤ C*B^(j+1)*WP.HigherOrder.scalarOrderWeight (M:ℝ) (j+1) p^(2*(j+1)) := by
  obtain ⟨Ω,R,C,B,M,hΩ,hΩv,hcover,hC,hB,hM,hR,hunit,hraw,hR0,hR',hA,hAne,hca,hInv⟩:=common_complex_inverse_cusp_bounds P
  have hc:(y₀:ℂ)∈Ω:=hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  obtain ⟨ε,hε,hεsub⟩:=Metric.isOpen_iff.mp hΩ (y₀:ℂ) hc
  let R₀:=ε/2
  have hR₀:0<R₀:=by dsimp[R₀];positivity
  have hball:Metric.closedBall (y₀:ℂ) R₀⊆Ω:=by
    intro z hz
    apply hεsub
    rw[Metric.mem_ball]
    have hb:=Metric.mem_closedBall.mp hz
    dsimp[R₀] at hb
    linarith
  have hdR:=WP.Analysis.dslope_analyticOnNhd_complex Ω hΩ R hR y₀ hc
  let d:ℂ→ℂ:=fun z=>kernelA R z*dslope R (y₀:ℂ) z
  have hda:AnalyticOnNhd ℂ d Ω:=hA.mul hdR
  let S:Set ℂ:=Complex.ofReal '' Icc (0:ℝ) y₀
  have hSc:IsCompact S:=isCompact_Icc.image Complex.continuous_ofReal
  have hSΩ:S⊆Ω:=by rintro z ⟨Y,hY,rfl⟩;exact hcover Y hY
  have hdc:∀z∈Ω,∀w:ℂ,ContinuousAt (fun a : ℂ × ℂ => d a.1) (z,w):=by
    intro z hz w
    simpa only[Function.comp_def] using (hda z hz).continuousAt.comp
      (continuous_fst.continuousAt : ContinuousAt (Prod.fst : ℂ × ℂ → ℂ) (z,w))
  have hdzero:∀z∈S,∀w∈({0}:Set ℂ),d z≠0:=by
    rintro z ⟨Y,hY,rfl⟩ w hw
    dsimp[d]
    apply mul_ne_zero (hAne _ (hcover Y hY))
    by_cases he:Y=y₀
    · subst Y
      rw[dslope_same,hR']
      norm_num
    · have hYi:Y∈Ico (0:ℝ) y₀:=⟨hY.1,lt_of_le_of_ne hY.2 he⟩
      have hne:R (Y:ℂ)≠0:=by rw[hraw Y hYi];exact_mod_cast (r_pos Y hYi).ne'
      intro hz
      have hf:=sub_smul_dslope R (y₀:ℂ) (Y:ℂ)
      simp only[hz,smul_zero,hR0,sub_zero] at hf
      exact hne hf.symm
  obtain ⟨W,hW,hSW,hWC,hWΩ,Md,hMd,hdb⟩:=WP.Analysis.compact_nonzero_parameter_uniform_bound
    Ω S {0} hΩ hSc isCompact_singleton (singleton_nonempty 0) hSΩ (fun z _=>d z) (fun z _=>d z) hdc hdc hdzero
  have hcoverW:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈W:=fun Y hY=>hSW ⟨Y,hY,rfl⟩
  obtain ⟨V,hV,hVconv,hVcover,hVW⟩:=WP.Analysis.exists_convex_physical_neighborhood W hW hcoverW
  have hVΩ:V⊆Ω:=hVW.trans (subset_closure.trans hWΩ)
  refine ⟨V,2*Md*C/R₀,B,M,hV,hVconv,hVcover,by positivity,hB,hM,?_⟩
  intro p j hp hj
  let G:ℂ→ℂ:=transportCoefficient P R p j
  let Mj:ℝ:=C*B^(j+1)*WP.HigherOrder.scalarOrderWeight (M:ℝ) (j+1) p^(2*(j+1))
  have hMj:0 ≤ Mj:=by dsimp[Mj,WP.HigherOrder.scalarOrderWeight];positivity
  have hG:AnalyticOnNhd ℂ G Ω:=transportCoefficient_analyticOnNhd Ω P R p j (fun n=>hca n p hp)
  have hGr(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀):G (Y:ℂ)=(WP.HigherOrder.transportCoefficient P p j Y:ℂ):=
    transportCoefficient_restrict_closed Ω hΩ hcover P R hR hR0 hraw hunit p j Y hY
  have hG0:G (y₀:ℂ)=0:=by
    rw[hGr y₀ ⟨y₀_pos.le,le_rfl⟩,WP.HigherOrder.transportCoefficient_critical_of_recursiveRemainder P
      (WP.HigherOrder.canonical_uniform_recursive_remainders P) p j hp hj]
    rfl
  have hGb:∀z∈Ω,‖G z‖ ≤ Mj:=fun z hz=>hInv (j+1) p hp z hz
  have hdG:=WP.Analysis.dslope_analyticOnNhd_complex Ω hΩ G hG y₀ hc
  let F:ℂ→ℂ:=fun z=>dslope G (y₀:ℂ) z/d z
  refine ⟨F,?_,?_,?_⟩
  · intro z hz
    exact (hdG z (hVΩ hz)).div (hda z (hVΩ hz)) (hdb z (subset_closure (hVW hz)) 0 (mem_singleton 0)).1
  · intro Y hYi
    have hYc:Y∈Icc (0:ℝ) y₀:=⟨hYi.1,hYi.2.le⟩
    have hδ:(Y:ℂ)-(y₀:ℂ)≠0:=sub_ne_zero.mpr (by exact_mod_cast ne_of_lt hYi.2)
    have hAa:kernelA R (Y:ℂ)≠0:=hAne _ (hcover Y hYc)
    have hRa:R (Y:ℂ)≠0:=by rw[hraw Y hYi];exact_mod_cast (r_pos Y hYi).ne'
    have hval:F (Y:ℂ)=G (Y:ℂ)/(kernelA R (Y:ℂ)*R (Y:ℂ)):=by
      dsimp only[F,d]
      rw[dslope_of_ne G (by exact_mod_cast ne_of_lt hYi.2),dslope_of_ne R (by exact_mod_cast ne_of_lt hYi.2)]
      simp only[slope,hG0,hR0,vsub_eq_sub,sub_zero,smul_eq_mul]
      field_simp[hδ,hAa,hRa]
    have hAr:kernelA R (Y:ℂ)=(A Y:ℂ):=(actual_kernel_inputs_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit Y hYc).1
    rw[hGr Y hYc,hAr,hraw Y hYi] at hval
    simpa only[Complex.ofReal_div,Complex.ofReal_mul] using hval
  · intro z hz
    have hDb:‖(d z)⁻¹‖ ≤ Md:=(hdb z (subset_closure (hVW hz)) 0 (mem_singleton 0)).2.1
    have hDs:=WP.Analysis.dslope_uniform_norm_bound Ω (y₀:ℂ) R₀ Mj hR₀ hMj hball G hG hG0 hGb z (hVΩ hz)
    dsimp only[F]
    rw[div_eq_mul_inv,norm_mul]
    have hb:=mul_le_mul hDs hDb (norm_nonneg _) (by positivity:0 ≤ 2*Mj/R₀)
    apply hb.trans_eq
    dsimp[Mj]
    ring
end WP.HigherOrder.ComplexCanonical
namespace WP.HigherOrder
lemma successor_factorial_square_geometric (j:ℕ) :
    ((j+1).factorial:ℝ)^2 ≤ (4:ℝ)^j*(j.factorial:ℝ)^2 := by
  have hn:((j+1:ℕ):ℝ) ≤ (2:ℝ)^j:=by exact_mod_cast j.lt_two_pow_self.succ_le
  have hs:=pow_le_pow_left₀ (Nat.cast_nonneg (j+1) : (0:ℝ) ≤ (j+1:ℕ)) hn 2
  have hsq:((j+1:ℕ):ℝ)^2 ≤ (4:ℝ)^j:=by
    apply hs.trans_eq
    rw[←pow_mul,Nat.mul_comm j 2,pow_mul]
    norm_num
  rw[Nat.factorial_succ,Nat.cast_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
end WP.HigherOrder
namespace WP.HigherOrder.ComplexCanonical
open Set
lemma common_transport_quotient_gevrey_two (P:PsiTheory)(p:ℕ)(hp:1 ≤ p) :
    ∃(V:Set ℂ)(C B:ℝ),IsOpen V ∧ Convex ℝ V ∧
      (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈V) ∧0<C ∧0<B ∧
      ∀j:ℕ,1 ≤ j→∃F:ℂ→ℂ,AnalyticOnNhd ℂ F V ∧
        (∀Y∈Ico (0:ℝ) y₀,F (Y:ℂ)=((WP.HigherOrder.transportCoefficient P p j Y/(A Y*r Y):ℝ):ℂ)) ∧
        ∀z∈V,‖F z‖ ≤ C*B^j*(j.factorial:ℝ)^2 := by
  obtain ⟨V,C,B,M,hV,hVconv,hcover,hC,hB,hM,hfamily⟩:=common_transport_quotient_order_bounds P
  let Q:ℝ:=((p:ℝ)+M)^2*Real.exp 2
  let R:ℝ:=B*Q
  have hpR:(1:ℝ) ≤ p:=by exact_mod_cast hp
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast hM
  have hQ:0<Q:=by dsimp[Q];positivity
  have hR:0<R:=by dsimp[R];positivity
  refine ⟨V,C*R,4*R,hV,hVconv,hcover,by positivity,by positivity,?_⟩
  intro j hj
  obtain ⟨F,hFa,hFr,hFb⟩:=hfamily p j hp hj
  refine ⟨F,hFa,hFr,?_⟩
  intro z hz
  have hweight:=WP.HigherOrder.fixed_marking_order_weight_factorial (M:ℝ) (Nat.cast_nonneg _) p (j+1) (by omega)
  have hbound:‖F z‖ ≤ C*R^(j+1)*((j+1).factorial:ℝ)^2:=by
    apply (hFb z hz).trans
    have ht:=mul_le_mul_of_nonneg_left hweight (by positivity:0 ≤ C*B^(j+1))
    convert ht using 1 <;>dsimp[R,Q]<;>rw[mul_pow]<;>ring
  apply hbound.trans
  have ht:=mul_le_mul_of_nonneg_left (WP.HigherOrder.successor_factorial_square_geometric j)
    (by positivity:0 ≤ C*R^(j+1))
  convert ht using 1 <;>rw[pow_succ,mul_pow]<;>ring
end WP.HigherOrder.ComplexCanonical
