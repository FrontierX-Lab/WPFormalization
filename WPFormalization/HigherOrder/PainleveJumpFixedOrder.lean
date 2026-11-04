import WPFormalization.HigherOrder.PainleveInstantonScaling
import WPFormalization.HigherOrder.PainleveJumpDefinitions
import WPFormalization.Analysis.PainleveNativeCoordinates
/-! The mature fixed-order GIKM expansion in the actual Boutroux variable.
The coordinate power identities and action rescaling identify every retained
coefficient with the uniquely determined rational jump table. Constants may
still depend on the fixed order; no Gevrey estimate is claimed here. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma painleveJumpCoordinate_pos (ξ:ℝ) (hξ:0<ξ) : 0<painleveJumpCoordinate ξ :=
  Real.rpow_pos_of_pos (div_pos hξ painleveAction_pos) _
lemma painleveJumpCoordinate_action (ξ:ℝ) (hξ:0<ξ) :
    External.painleveAction*Real.rpow (painleveJumpCoordinate ξ) (5/4:ℝ)=ξ := by
  simp only [painleveJumpCoordinate,Real.rpow_eq_pow]
  rw [←Real.rpow_mul (div_pos hξ painleveAction_pos).le]
  norm_num
  field_simp [painleveAction_pos.ne']
lemma painleveJumpCoordinate_inverse_power (ξ:ℝ) (hξ:0<ξ) (j:ℕ) :
    Real.rpow (painleveJumpCoordinate ξ) (-5*(j:ℝ)/4)=
      External.painleveAction^j/ξ^j := by
  simp only [painleveJumpCoordinate,Real.rpow_eq_pow]
  rw [←Real.rpow_mul (div_pos hξ painleveAction_pos).le,
    show (4/5:ℝ)*(-5*(j:ℝ)/4)=-(j:ℝ) by ring,
    Real.rpow_neg (div_pos hξ painleveAction_pos).le,Real.rpow_natCast,div_pow,inv_div]

lemma normalizedPainleveJump_fixed_order (G:External.PainleveAnalytic.GIKMData) (m:ℕ) :
    ∃C R:ℝ,0<C ∧ 0<R ∧ ∀ξ:ℝ,R≤ξ →
      ‖normalizedPainleveJump G ξ-
        ∑j∈Finset.range (m+1),((jumpCoefficient j:ℝ):ℂ)/(ξ:ℂ)^j‖≤C/ξ^(m+1) := by
  obtain ⟨C,T,hC,hT,he⟩:=G.fixed_order_jump m
  obtain ⟨R,hR,hRadius⟩:=WP.Analysis.native_radius_eventually_large T
  have hA:=painleveAction_pos
  refine ⟨C*External.painleveAction^(m+1),R,by positivity,hR,?_⟩
  intro ξ hξ
  have hξp : 0<ξ:=hR.trans_le hξ
  let Z:=painleveJumpCoordinate ξ
  have hZ : T≤Z := (hRadius ξ hξ).le
  have h := he Z hZ
  change ‖(G.u 1 (Z:ℂ)-G.u 0 (Z:ℂ))/
    (-External.PainleveAnalytic.S₁*Complex.exp (-((External.painleveAction*Real.rpow Z (5/4):ℝ):ℂ))*
      (Real.rpow Z (-1/8):ℂ))-
      ∑j∈Finset.range (m+1),(G.b j:ℂ)*(Real.rpow Z (-5*(j:ℝ)/4):ℂ)‖≤
    C*Real.rpow Z (-5*((m+1:ℕ):ℝ)/4) at h
  have ha : External.painleveAction*Real.rpow Z (5/4:ℝ)=ξ := painleveJumpCoordinate_action ξ hξp
  rw [ha,painleveJumpCoordinate_inverse_power ξ hξp (m+1)] at h
  have hs : (∑j∈Finset.range (m+1),(G.b j:ℂ)*(Real.rpow Z (-5*(j:ℝ)/4):ℂ))=
      ∑j∈Finset.range (m+1),((jumpCoefficient j:ℝ):ℂ)/(ξ:ℂ)^j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [painleveJumpCoordinate_inverse_power ξ hξp j]
    have hb := congrArg (fun r:ℝ=>(r:ℂ)) (instantonCoefficient_rescaling G j)
    push_cast at hb ⊢
    rw [←hb]
    ring
  rw [hs] at h
  change ‖normalizedPainleveJump G ξ-∑j∈Finset.range (m+1),
    ((jumpCoefficient j:ℝ):ℂ)/(ξ:ℂ)^j‖≤_ at h
  convert h using 1 <;> ring
end WP.HigherOrder
