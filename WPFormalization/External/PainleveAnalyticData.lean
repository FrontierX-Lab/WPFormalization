import WPFormalization.External.Painleve
import WPFormalization.HigherOrder.PainleveFormalRecurrences

/-! Mature analytic Painleve I data, isolated from the new WP proofs.

PI-CONTOUR: GIKM arXiv:1002.3634v3, printed pp.2,7-13, Eqs.(1.3),(1.7),
(2.3)-(2.9),(2.14),(2.25),(2.29)-(2.33),(2.40)-(2.45). The contour uses
5g-2 from the defining Eq.(2.14), not the inconsistent exponent printed in
(2.26). Its radius is fixed before a uniform-in-g error constant. All
algebraic and jump truncation constants may depend on the fixed order.

PI-BOREL: CCH arXiv:1310.5330v2, Theorem2, Proposition3(i),(ii), Lemma17(c),(f),
printed pp.3,4,12. The chosen single-valued slit continuation and exact
zero-parameter positive-real off-ray formula include ordinary monodromy/
identity-principle corollaries, not verbatim source statements. Native
analyticity is quantified with angular margins, not one radius up to a sector
boundary. The Stokes multiplier remains symbolic.

The two Nonempty assertions below defer only these mature classical packages.
No actual GIKM-to-native adapter, coordinate change, leading-multiplier match,
uniform jump remainder, Gevrey bound, or endpoint/WP estimate is a field.
Those are new local proof obligations and are defined outside this module. -/
noncomputable section
namespace WP.External.PainleveAnalytic
open Set Filter MeasureTheory Complex
open scoped Topology

abbrev action : ℝ := WP.External.painleveAction
noncomputable def S₁ : ℂ := -(WP.External.stokesAmplitude : ℂ)*Complex.I
noncomputable def ray (φ t : ℝ) : ℂ := (t:ℂ)*Complex.exp (Complex.I*(φ:ℂ))
noncomputable def polarPower (t φ q : ℝ) : ℂ :=
  (Real.rpow t q:ℂ)*Complex.exp (Complex.I*((q*φ:ℝ):ℂ))
noncomputable def algebraicPolynomial (a : ℕ → ℚ) (N : ℕ) (t φ : ℝ) : ℂ :=
  ∑ g ∈ Finset.range (N+1), (a g:ℂ)*
    polarPower t φ (1/2-5*(g:ℝ)/2)

noncomputable def gikmSector (k : ℤ) (ε R : ℝ) : Set ℂ :=
  {z | ∃ t φ : ℝ, R<t ∧ -6*Real.pi/5+4*Real.pi*k/5+ε<φ ∧
      φ<2*Real.pi/5+4*Real.pi*k/5-ε ∧ z=ray φ t}

/- Classical package G. It contains the actual GIKM functions and
a source coefficient sequence constrained by its full rational recurrence.
The adapter below proves identity with the project table; it is not an input. -/
@[blueprint "ext:painleve-contour"]
structure GIKMData where
  u : ℤ → ℂ → ℂ
  a : ℕ → ℚ
  a_zero : a 0 = 1
  a_recursion : ∀ n : ℕ, a (n+1) = ((25*(n:ℚ)^2-1)/48)*a n-
    (1/2:ℚ)*∑ j ∈ Finset.Icc 1 n, a j*a (n+1-j)
  b : ℕ → ℝ
  b_zero : b 0 = 1
  /- GIKM (1.7), printed p.2, shifted from n to n+1.
  The n-term range is empty for the first coefficient. Odd half-indices vanish. -/
  b_recursion : ∀ n:ℕ, b (n+1) = 8/(25*action*((n+1:ℕ):ℝ))*
    (12*(∑ l∈Finset.range n,b l*
      (if (n+2-l)%2=0 then (a ((n+2-l)/2):ℝ) else 0))-
      (25/64:ℝ)*(2*(n:ℝ)+1)^2*b n)
  periodic : ∀ k z, u (k+5) z=u k z
  rotation : ∀ k z,
    u k z=Complex.exp (-Complex.I*((8*Real.pi*k/5:ℝ):ℂ))*
      u 0 (Complex.exp (-Complex.I*((4*Real.pi*k/5:ℝ):ℂ))*z)
  sector_analytic : ∀ k ε, 0<ε → ε<4*Real.pi/5 →
    ∃ R : ℝ, 0<R ∧ AnalyticOnNhd ℂ (u k) (gikmSector k ε R)
  ode : ∀ k z, AnalyticAt ℂ (u k) z →
    deriv (deriv (u k)) z=6*(u k z)^2-6*z
  /- GIKM (2.3),(2.6), pp.7-8: FIXED N constants; no order control. -/
  fixed_algebraic : ∀ (k:ℤ) (N:ℕ) ε, 0<ε → ε<4*Real.pi/5 →
    ∃ C R : ℝ, 0<C ∧ 0<R ∧ ∀ t φ : ℝ, R≤t →
      -6*Real.pi/5+4*Real.pi*k/5+ε≤φ →
      φ≤2*Real.pi/5+4*Real.pi*k/5-ε →
      ‖u k (ray φ t)-algebraicPolynomial a N t φ‖ ≤
        C*Real.rpow t (-(5*(N:ℝ)+4)/2)
  /- GIKM (2.7)-(2.9), pp.7-8. Only the fixed leading jump. -/
  fixed_leading_jump : ∃ C R : ℝ, 0<C ∧ 0<R ∧ ∀ Z : ℝ, R≤Z →
    ‖(u 1 (Z:ℂ)-u 0 (Z:ℂ))/
        (-S₁*Complex.exp (-((action*Real.rpow Z (5/4):ℝ):ℂ))*
          (Real.rpow Z (-1/8):ℂ))-1‖ ≤ C*Real.rpow Z (-5/4)
  /- GIKM (2.40)-(2.45), printed pp.12-13: every FIXED m has its own
  constants and threshold. No factorial or uniform dependence on m is licensed. -/
  fixed_order_jump : ∀ m:ℕ,∃ C R:ℝ,0<C ∧ 0<R ∧ ∀Z:ℝ,R≤Z →
    ‖(u 1 (Z:ℂ)-u 0 (Z:ℂ))/
        (-S₁*Complex.exp (-((action*Real.rpow Z (5/4):ℝ):ℂ))*
          (Real.rpow Z (-1/8):ℂ))-
      (∑ j∈Finset.range (m+1),(b j:ℂ)*(Real.rpow Z (-5*(j:ℝ)/4):ℂ))‖ ≤
        C*Real.rpow Z (-5*((m+1:ℕ):ℝ)/4)
  contour_radius : ℝ
  contour_radius_pos : 0<contour_radius
  /- GIKM (2.33), (2.30), p.11, with integrability made explicit.
  Only a fixed rho is needed: C_rho precedes g, and no Taylor order occurs. -/
  coefficient_contour : ∀ ρ : ℝ, contour_radius≤ρ →
    ∃ Cρ:ℝ,0<Cρ ∧ ∀ (g:ℕ),1≤g →
      IntegrableOn (fun t:ℝ => ((t^(5*g-2):ℝ):ℂ)*
        (u 1 ((t^2:ℝ):ℂ)-u 0 ((t^2:ℝ):ℂ))) (Ici ρ) ∧
      ‖(a g:ℂ)+(5/(2*(Real.pi:ℂ)*Complex.I))*
        ∫ t in Ici ρ, ((t^(5*g-2):ℝ):ℂ)*
          (u 1 ((t^2:ℝ):ℂ)-u 0 ((t^2:ℝ):ℂ))‖ ≤ Cρ*ρ^(5*g)

/- OWN exact coefficient identification from the already proved recurrence uniqueness. -/
lemma GIKMData.sourceCoefficient_eq_actual (G : GIKMData) :
    G.a = HigherOrder.zeroInstantonCoefficient :=
  HigherOrder.zeroInstantonCoefficient_unique G.a G.a_zero G.a_recursion

/- OWN contour adapter: no new coefficient-contour axiom is required. -/
lemma GIKMData.actual_coefficient_contour (G : GIKMData)
    (ρ : ℝ) (hρ : G.contour_radius ≤ ρ) :
    ∃ Cρ:ℝ,0<Cρ ∧ ∀ (g:ℕ),1≤g →
      IntegrableOn (fun t:ℝ => ((t^(5*g-2):ℝ):ℂ)*
        (G.u 1 ((t^2:ℝ):ℂ)-G.u 0 ((t^2:ℝ):ℂ))) (Ici ρ) ∧
      ‖(HigherOrder.zeroInstantonCoefficient g:ℂ)+
        (5/(2*(Real.pi:ℂ)*Complex.I))*
          ∫ t in Ici ρ, ((t^(5*g-2):ℝ):ℂ)*
            (G.u 1 ((t^2:ℝ):ℂ)-G.u 0 ((t^2:ℝ):ℂ))‖ ≤ Cρ*ρ^(5*g) := by
  obtain ⟨C,hC,h⟩ := G.coefficient_contour ρ hρ
  refine ⟨C,hC,?_⟩
  intro g hg
  simpa only [G.sourceCoefficient_eq_actual] using h g hg

inductive Side | upper | lower deriving DecidableEq
noncomputable def sideSign : Side → ℝ | .upper => 1 | .lower => -1
noncomputable def nativeDomain (s : Side) (ε R : ℝ) : Set ℂ :=
  {z | ∃ t φ : ℝ, R<t ∧ -Real.pi/2+ε<sideSign s*φ ∧
      sideSign s*φ<3*Real.pi/4 ∧ z=ray φ t}

/- Native CCH PI(6) conditions, before selecting its exponential parameter.
The extended quarter contains the selected anti-Stokes ray. -/
structure NativeSmall (s : Side) (h : ℂ → ℂ) : Prop where
  analytic : ∀ ε:ℝ,0<ε → ε<Real.pi/4 →
    ∃ R : ℝ, 0<R ∧ AnalyticOnNhd ℂ h (nativeDomain s ε R)
  ode : ∀ z, (∃ ε R:ℝ,0<ε ∧ ε<Real.pi/4 ∧ 0<R ∧ z∈nativeDomain s ε R) →
    AnalyticAt ℂ h z →
    deriv (deriv h) z+deriv h z/z-h z-(h z)^2/2-(392/625:ℂ)/z^4=0
  right_decay : ∀ ε:ℝ,0<ε → ε<Real.pi/2 →
    ∃ C R:ℝ,0<C ∧ 0<R ∧ ∀t φ:ℝ,R≤t → |φ|≤Real.pi/2-ε →
      ‖h (ray φ t)‖≤C*Real.rpow t (-4)

noncomputable def borelSlit : Set ℂ := {z | z.im≠0 ∨ |z.re|<1}
noncomputable def laplaceAlong (H : ℂ → ℂ) (φ ξ : ℝ) : ℂ :=
  ∫ t in Ioi (0:ℝ), Complex.exp (-(ξ:ℂ)*ray φ t)*H (ray φ t)*
    Complex.exp (Complex.I*(φ:ℂ))

/- Classical package B: a single canonical Borel germ and its
chosen continuation on a fixed slit domain. No numerical CCH Stokes value. -/
@[blueprint "ext:painleve-borel"]
structure CCHData where
  H₀ : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ H₀ borelSlit
  S : ℂ
  α : ℂ → ℂ
  β : ℂ → ℂ
  r : ℝ
  r_pos : 0<r
  r_small : r<1/4
  alpha_analytic : AnalyticOnNhd ℂ α (Metric.closedBall (1:ℂ) (2*r))
  beta_analytic : AnalyticOnNhd ℂ β (Metric.closedBall (1:ℂ) (2*r))
  alpha_one : α 1=1
  /- CCH Proposition 3(i), p.4, with usual sqrt positive at real p<1. -/
  local_form : ∀ z∈Metric.ball (1:ℂ) (2*r), z∈borelSlit →
    H₀ z=S*(Complex.sqrt (1-z))⁻¹*α z+β z
  /- Lemma 17(c),(f), p.12; only fixed non-Stokes rays are requested.
  b and U may depend on phi. No uniformity over phi is assumed. -/
  fixed_ray_L1 : ∀ φ:ℝ, 0 < |φ| → |φ| < Real.pi/2 →
    ∃ b U:ℝ,0<b ∧ 0<U ∧
      IntegrableOn (fun t:ℝ=>Real.exp (-b*t)*‖H₀ (ray φ t)‖) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ),Real.exp (-b*t)*‖H₀ (ray φ t)‖)≤U
  parameter : Side → (ℂ → ℂ) → ℂ
  /- Native part of CCH Thm2(i), p.3. Boundary decay below will force C=0
  in a LOCAL PROOF; it is not an actual GIKM normalization input here. -/
  parameter_limit : ∀ s h,NativeSmall s h →
    Tendsto (fun t:ℝ=>Complex.sqrt (ray (sideSign s*Real.pi/2) t)*
      Complex.exp (ray (sideSign s*Real.pi/2) t)*h (ray (sideSign s*Real.pi/2) t))
      atTop (nhds (parameter s h))
  /- Zero-parameter case of CCH Thm2(ii), followed by the analytic continuation
  in Proposition3(ii). Fixed phi and xi0 precede xi, and no Taylor order occurs.
  Analytic continuation from the matching ray to real xi is the only classical
  corollary bundled here; it may instead be proved by the identity theorem. -/
  zero_parameter_sum : ∀ s h,NativeSmall s h → parameter s h=0 →
    ∀ φ:ℝ,0<φ → φ<Real.pi/2 → ∃ ξ₀:ℝ,0<ξ₀ ∧ ∀ξ:ℝ,ξ₀≤ξ →
      h (ξ:ℂ)=laplaceAlong H₀ (-sideSign s*φ) ξ


/- Classical existence of the specified normalized GIKM family. -/
@[blueprint "ext:painleve-contour"]
theorem exists_gikm_data : Nonempty GIKMData := by
  sorry

/- Classical Borel germ/continuation and native exact representation data. -/
@[blueprint "ext:painleve-borel"]
theorem exists_cch_data : Nonempty CCHData := by
  sorry

end WP.External.PainleveAnalytic
