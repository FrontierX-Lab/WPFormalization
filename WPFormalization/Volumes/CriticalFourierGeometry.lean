import WPFormalization.Volumes.CriticalGaussianCoordinates
import WPFormalization.Volumes.MarkedFourierInversion
/-! The genuine critical variance has a uniform positive square-root lower bound, and the actual centered generating function agrees with the scaled Fourier transform on its real period. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma CriticalGaussianCoordinateData.critical_variance_sqrt_lower (d:CriticalGaussianCoordinateData) :
    ∃R b:ℝ,0<R ∧ R<y₀ ∧ 0<b ∧ ∀δ∈Ioo (0:ℝ) R,
      b≤Real.sqrt (WP.euler WP.Psi (XR (y₀-δ))) := by
  let M:ℝ:=‖d.L 0‖+1
  have hM:0<M:=by dsimp[M];positivity
  have hn:‖d.L 0‖<M:=by dsimp[M];linarith
  have hLb:∀ᶠδ:ℂ in 𝓝 0,‖d.L δ‖≤M:=
    (d.L_analytic.continuousAt.norm.tendsto.eventually (eventually_lt_nhds hn)).mono (fun δ hδ=>hδ.le)
  obtain ⟨Rn,hRn,hLa,hqa,hUa,haxis,hfold,hphysical⟩:=d.common_neighborhood
  obtain ⟨Rl,hRl,hLball⟩:=Metric.eventually_nhds_iff.mp hLb
  let R:ℝ:=min Rn (min Rl (y₀/2))/2
  have hR:0<R:=half_pos (lt_min hRn (lt_min hRl (half_pos y₀_pos)))
  have hRRn:R<Rn:=(half_lt_self (lt_min hRn (lt_min hRl (half_pos y₀_pos)))).trans_le (min_le_left _ _)
  have hRRl:R<Rl:=(half_lt_self (lt_min hRn (lt_min hRl (half_pos y₀_pos)))).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hRy:R<y₀:=((half_lt_self (lt_min hRn (lt_min hRl (half_pos y₀_pos)))).trans_le ((min_le_right _ _).trans (min_le_right _ _))).trans (half_lt_self y₀_pos)
  let b:ℝ:=(R^2*M)⁻¹
  have hb:0<b:=by dsimp[b];positivity
  refine ⟨R,b,hR,hRy,hb,?_⟩
  intro δ hδ
  have hYp:0<y₀-δ:=by linarith[hδ.2]
  have hYlt:y₀-δ<y₀:=by linarith[hδ.1]
  have hx:XR (y₀-δ)∈Ioo (0:ℝ) xCritical:=by
    constructor
    · simpa only[XR_zero] using XR_strictMonoOn (show (0:ℝ)∈Iic y₀ from y₀_pos.le) (show y₀-δ∈Iic y₀ from hYlt.le) hYp
    · exact XR_strictMonoOn (show y₀-δ∈Iic y₀ from hYlt.le) (show y₀∈Iic y₀ from by simp) hYlt
  have hv:0<WP.euler WP.Psi (XR (y₀-δ)):=mul_pos hx.1 (Psi_deriv_pos_interior _ ⟨hx.1.le,hx.2⟩)
  have hs:0<Real.sqrt (WP.euler WP.Psi (XR (y₀-δ))):=Real.sqrt_pos.mpr hv
  have hunit:=(hphysical δ ⟨hδ.1,hδ.2.trans hRRn⟩).1
  have hnorm:=congrArg norm hunit
  have hDL:‖d.L (δ:ℂ)‖≤M:=hLball (by rw[dist_zero_right,Complex.norm_of_nonneg hδ.1.le];exact hδ.2.trans hRRl)
  simp only[norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ.1,
    abs_of_nonneg (inv_nonneg.mpr hs.le)] at hnorm
  have hbound:(Real.sqrt (WP.euler WP.Psi (XR (y₀-δ))))⁻¹≤R^2*M:=by
    rw[←hnorm]
    exact mul_le_mul (pow_le_pow_left₀ hδ.1.le hδ.2.le 2) hDL (norm_nonneg _) (sq_nonneg _)
  have hm:0<R^2*M:=by positivity
  have hb0:1/Real.sqrt (WP.euler WP.Psi (XR (y₀-δ)))≤R^2*M:=by simpa only[one_div] using hbound
  have he:1≤(R^2*M)*Real.sqrt (WP.euler WP.Psi (XR (y₀-δ))):=(div_le_iff₀ hs).mp hb0
  change (R^2*M)⁻¹≤_
  rw[←one_div]
  exact (div_le_iff₀ hm).mpr (by simpa only[mul_comm] using he)

lemma scaledMarkedFourier_eq_centered_on_period
    (P:PsiTheory)(g p k:ℕ)(x t:ℝ)
    (hroot:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x)
    (ht:t∈Icc (-(Real.pi*Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)))
      (Real.pi*Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x))) :
    scaledMarkedFourier P g p x t=centeredMarkedGenerating P g p k x
      (Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)) (Complex.I*(t:ℂ)) := by
  dsimp only[scaledMarkedFourier,scaledCenteredFourier]
  rw[Set.indicator_of_mem ht]
  dsimp only[markedPGF,centeredMarkedGenerating]
  have hk:(k:ℂ)=((complexity g p:ℝ):ℂ)*(WP.Psi x:ℂ):=by exact_mod_cast hroot
  rw[hk]
  have he:(((t/Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x):ℝ):ℂ))*Complex.I=
      Complex.I*(t:ℂ)/(Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x):ℂ):=by push_cast;ring
  rw[he]
  congr 2 <;>push_cast <;>ring
end WP.Analysis
