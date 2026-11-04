# Classical results used by the project

These are the 77 groups of classical dependencies registered for stage one. Each entry records the precise statement and conditions, references, and corresponding Lean names.
"Proof required" means that a classical result still uses `sorry`. "Instance required" means that its properties are fields of a structure; we still need to prove that the intended mathematical objects satisfy them.
Auxiliary declarations already proved within a group are not outstanding obligations. See [Remaining infrastructure](INFRASTRUCTURE.md) for the specific work left.

<a id="external-inputs"></a>

## List

1. [Classical identities for psi intersection numbers](#input-int-psi) (INT-PSI)
2. [Cohomology classes and integration on moduli spaces](#input-int-coh) (INT-COH)
3. [The mixed kappa–psi intersection transform](#input-int-kmz) (INT-KMZ)
4. [The intersection polynomial for WP volumes](#input-wp-poly) (WP-POLY)
5. [The one-point psi intersection formula](#input-int-one) (INT-ONE)
6. [An upper bound for two-point psi intersections](#input-int-two) (INT-TWO)
7. [The endpoint identity for intersections and Painlevé coefficients](#input-pi-iz) (PI-IZ)
8. [Classical large-order asymptotics of Painlevé coefficients](#input-pi-leading) (PI-LEADING)
9. [Gamma ratio estimates with fixed parameter shifts](#input-sf-gamma-ratio) (SF-GAMMA-RATIO)
10. [Stirling remainder bounds for the real Gamma function](#input-sf-gamma-stirling) (SF-GAMMA-STIRLING)
11. [The Binet remainder and Laplace representation for log Gamma](#input-sf-binet) (SF-BINET)
12. [Zeros of the Bessel J0 function](#input-bessel-j0) (BESSEL-J0)
13. [Analytic implicit functions and convergence of formal branches](#input-gen-analytic-ift) (GEN-ANALYTIC-IFT)
14. [The first integrated KdV identity for pure psi intersections](#input-int-kdv) (INT-KDV)
15. [Real-axis singularities of nonnegative power series](#input-gen-pringsheim) (GEN-PRINGSHEIM)
16. [Counting complex zeros with multiplicity](#input-gen-rouche) (GEN-ROUCHE)
17. [Product factorization of entire functions of finite order](#input-gen-hadamard) (GEN-HADAMARD)
18. [WP volume asymptotics with a fixed number of cusps](#input-wp-mz-fixed) (WP-MZ-FIXED)
19. [Contour representations and fixed-order jumps for Painlevé I](#input-pi-contour) (PI-CONTOUR)
20. [The Borel representation of Painlevé I](#input-pi-borel) (PI-BOREL)
21. [Nef intersection inequalities and their realization on moduli spaces](#input-int-nef) (INT-NEF)
22. [Volume asymptotics at fixed genus with increasing cusp count](#input-wp-mz-fixed-genus) (WP-MZ-FIXED-GENUS)
23. [Curves on hyperbolic surfaces and measurable length counts](#input-hyp-curves) (HYP-CURVES)
24. [Discrete spectra and local variational estimates on pairs of pants](#input-hyp-spectral) (HYP-SPECTRAL)
25. [A second-moment lower bound for short-pants counts](#input-wp-shen-wu-pants) (WP-SHEN-WU-PANTS)
26. [Cutting and integration for labeled multicurves](#input-hyp-multicurve-integration) (HYP-MULTICURVE-INTEGRATION)
27. [General upper bounds and critical-range lower bounds for WP volumes](#input-wp-sw-critical-volume) (WP-SW-CRITICAL-VOLUME)
28. [Simplicity and disjointness of short primitive geodesics](#input-hyp-collar) (HYP-COLLAR)
29. [Tight-boundary geometry and the moment transform](#input-tight-bz) (TIGHT-BZ)
30. [Higher logarithmic kappa intersections](#input-int-higher-kappa) (INT-HIGHER-KAPPA)
31. [Homotopy classes of closed geodesics after capping](#input-hyp-tight-curves) (HYP-TIGHT-CURVES)
32. [Orbit classification of ordered tight multicurves](#input-tight-cut-topology) (TIGHT-CUT-TOPOLOGY)
33. [Integration over restricted regions for tight multicurves](#input-bl-tight-integration) (BL-TIGHT-INTEGRATION)
34. [Extension and general-position properties of tight geodesic families](#input-bl-tight-geometry) (BL-TIGHT-GEOMETRY)
35. [The measurable structure on point-measure spaces](#input-prob-point-borel) (PROB-POINT-BOREL)
36. [A factorial-moment criterion for Poisson limits with positive rates](#input-prob-factorial-pos) (PROB-FACTORIAL-POS)
37. [Extending the factorial-moment criterion to zero rates](#input-prob-factorial-zero) (PROB-FACTORIAL-ZERO)
38. [Existence of Poisson random point measures](#input-prob-ppp-exists) (PROB-PPP-EXISTS)
39. [Point-process convergence from window-count distributions](#input-prob-vague-counts) (PROB-VAGUE-COUNTS)
40. [Measurability of unordered multicurve observables](#input-mc-count-borel) (MC-COUNT-BOREL)
41. [Countable geodesic labels and measurable moduli quotients](#input-hyp-tight-borel) (HYP-TIGHT-BOREL)
42. [Hyperbolic quotient surfaces and primitive geodesics](#input-hyp-surface-quotient) (HYP-SURFACE-QUOTIENT)
43. [Local geometry of hyperbolic disks and thin collars](#input-hyp-local-packing) (HYP-LOCAL-PACKING)
44. [Doubling surfaces along geodesic boundaries](#input-hyp-doubling) (HYP-DOUBLING)
45. [Compatibility of multicurve cutting with restriction](#input-mc-cut-restriction) (MC-CUT-RESTRICTION)
46. [Local comparison of geodesic arc endpoints](#input-hyp-arc-endpoint) (HYP-ARC-ENDPOINT)
47. [Intrinsic completions of subsurfaces and primitive curves](#input-hyp-intrinsic-pieces) (HYP-INTRINSIC-PIECES)
48. [The filling subsurface of one nonsimple geodesic](#input-hyp-single-filling) (HYP-SINGLE-FILLING)
49. [Geometric realization of cut components](#input-mc-cut-components) (MC-CUT-COMPONENTS)
50. [Comparison of genus-zero WP volumes with boundaries](#input-wp-genus0-boundary) (WP-GENUS0-BOUNDARY)
51. [Regular neighborhoods of finite graphs in surfaces](#input-top-regular-neighborhood) (TOP-REGULAR-NEIGHBORHOOD)
52. [Finite CW decompositions and Euler characteristics of surfaces](#input-top-surface-euler) (TOP-SURFACE-EULER)
53. [Marked families of pairs of pants with two cusps](#input-hyp-pants-family) (HYP-PANTS-FAMILY)
54. [Metric comparison under deformations of pairs of pants](#input-hyp-pants-deformation) (HYP-PANTS-DEFORMATION)
55. [Metric uniqueness of pairs of pants with two cusps](#input-hyp-pants-uniqueness) (HYP-PANTS-UNIQUENESS)
56. [The vague topology on point measures and positive rescaling](#input-prob-vague-topology) (PROB-VAGUE-TOPOLOGY)
57. [Geodesic straightening of closed-loop homotopy classes](#input-top-loop-straightening) (TOP-LOOP-STRAIGHTENING)
58. [Annuli between disjoint homotopic simple closed curves](#input-top-simple-annulus) (TOP-SIMPLE-ANNULUS)
59. [Simple closed curves, disks, and cusp ends](#input-top-simple-complement) (TOP-SIMPLE-COMPLEMENT)
60. [The Laplace functional of Poisson random measures](#input-prob-poisson-laplace) (PROB-POISSON-LAPLACE)
61. [Topology of finite interval gluings](#input-top-cyclic-interval) (TOP-CYCLIC-INTERVAL)
62. [Curve straightening on convex bordered hyperbolic surfaces](#input-hyp-bordered-loop) (HYP-BORDERED-LOOP)
63. [Intrinsic primitive traces and boundary uniqueness](#input-hyp-primitive-boundary) (HYP-PRIMITIVE-BOUNDARY)
64. [Axial geodesics in cusp ends and compact annuli](#input-hyp-peripheral-axial) (HYP-PERIPHERAL-AXIAL)
65. [Planar Jordan–Schoenflies extension](#input-top-planar-jordan) (TOP-PLANAR-JORDAN)
66. [Coordinates on planar annuli and punctured disks](#input-top-planar-regions) (TOP-PLANAR-REGIONS)
67. [Measurable compactly supported integrals and the vague topology](#input-prob-vague-pairing) (PROB-VAGUE-PAIRING)
68. [Convergence in distribution under almost-everywhere continuous maps](#input-prob-ae-cmt) (PROB-AE-CMT)
69. [The first arrival of a marked Poisson process](#input-prob-ppp-first) (PROB-PPP-FIRST)
70. [Convergence in distribution of the selected first point](#input-prob-first-cmt) (PROB-FIRST-CMT)
71. [Convex supporting subsurfaces for finite geodesic sets](#input-hyp-finite-support) (HYP-FINITE-SUPPORT)
72. [Fundamental groups of finite connected graphs](#input-top-graph-pi1) (TOP-GRAPH-PI1)
73. [Fundamental groups of orientable hyperbolic surfaces of finite area](#input-top-surface-pi1) (TOP-SURFACE-PI1)
74. [Restriction and independence of Poisson processes](#input-prob-ppp-restriction) (PROB-PPP-RESTRICTION)
75. [Convergence in distribution of point measures from Laplace functionals](#input-prob-pm-laplace-cmt) (PROB-PM-LAPLACE-CMT)
76. [Integrals and moments of Poisson point processes](#input-ppp-integral-moments) (PPP-INTEGRAL-MOMENTS)
77. [Figure-eight curves in hyperbolic pairs of pants](#input-hyp-pants-figure-eight) (HYP-PANTS-FIGURE-EIGHT)

## Statements, conditions, and references

<a id="input-int-psi"></a>

<details>
<summary>1. Classical identities for psi intersection numbers (INT-PSI)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-int-psi).

**Lean declarations**:

- [WP.PsiTheory](../WPFormalization/Statements/IntersectionInterface.lean#L36)

**Precise statement and conditions**: Stable g,n; signed descendant degrees; negative/unstable/wrong-dimensional terms vanish; string/dilaton stable children; DVV nonnegative tail and complexity≥2.

**Reference**: DGZZ, SIGMA 16 (2020),086, §1 Eqs.(1),(2), dilaton p.3; bases and uniqueness pp.2–3

[Read the source](https://sigma-journal.com/2020/086/sigma20-086.pdf).

**Used for**: Finite transforms, comparison recursion, endpoint string, marked and volume statements

</details>

<a id="input-int-coh"></a>

<details>
<summary>2. Cohomology classes and integration on moduli spaces (INT-COH)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-int-coh).

**Lean declarations**:

- [WP.External.DMClasses](../WPFormalization/External/IntersectionTheory.lean#L21)

**Precise statement and conditions**: Even tautological real cohomology, fundamental pairing; only top complex degree 3g−3+n integrates nontrivially; [ωWP]=2π²κ1.

**Reference**: Wolpert (1985), WP class relation; Liu–Xu arXiv:1103.5136v2 §1 Eq.(1),p.1

[Read the source](https://arxiv.org/pdf/1103.5136).

**Used for**: Normalized mixed intersections and physical WP volume polynomial

</details>

<a id="input-int-kmz"></a>

<details>
<summary>3. The mixed kappa–psi intersection transform (INT-KMZ)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-int-kmz).

**Lean declarations**:

- [WP.External.IntersectionRealization](../WPFormalization/External/IntersectionTheory.lean#L59)

**Precise statement and conditions**: Stable g,n; nonnegative degrees with D≤3g−3+n; m=N−D. The finite partition sum has coefficients ((−1)^(i+2)/(i+1)!)^l/l!.

**Reference**: Kaufmann–Manin–Zagier, alg-geom/9604001; exact normalized transform in Liu–Xu arXiv:1103.5136v2 Eq.(24),p.6

[Read the source](https://arxiv.org/pdf/1103.5136).

**Used for**: Geometry.geometricBracket_eq_model, then cusp and boundary volume bridges

</details>

<a id="input-wp-poly"></a>

<details>
<summary>4. The intersection polynomial for WP volumes (WP-POLY)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-wp-poly).

**Lean declarations**:

- [WP.External.WeilPeterssonGeometry](../WPFormalization/External/WeilPeterssonGeometry.lean#L25)

**Precise statement and conditions**: Stable g,n; all physical lengths L_i≥0. Finite orbifold symplectic measure ωWP^N/N! and exact polynomial in L_i^(2d_i)/(4^d_i(2d_i+1)!).

**Reference**: Mirzakhani,JAMS20(2007),1–23,volume/intersection theorem; normalization: Liu–Xu arXiv:1103.5136v2 §1 Eq.(1) and following boundary formula,p.1

[Read the source](https://arxiv.org/pdf/1103.5136).

**Used for**: Geometry.wpVolume_eq_boundaryVolumeModel and cuspVolume_eq_volumeModel; explicit G in Theorem1.1

</details>

<a id="input-int-one"></a>

<details>
<summary>5. The one-point psi intersection formula (INT-ONE)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-int-one).

**Lean declarations**:

- [WP.one_point](../WPFormalization/External/IntersectionEstimates.lean#L27)

**Precise statement and conditions**: P:PsiTheory; g≥1; pure P g [3g−2]=1/(24^g g!).

**Reference**: DGZZ SIGMA16(2020),086 §1 Eq.(4); Liu–Xu arXiv:1103.5136v2 p.3; transfer to arbitrary PsiTheory additionally uses classical DVV uniqueness (DGZZ pp.2–3)

[Read the source](https://sigma-journal.com/2020/086/sigma20-086.pdf).

**Used for**: Finite-genus primitive bounds and later comparison anchors

</details>

<a id="input-int-two"></a>

<details>
<summary>6. An upper bound for two-point psi intersections (INT-TWO)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-int-two).

**Lean declarations**:

- [WP.two_point](../WPFormalization/External/IntersectionEstimates.lean#L37)

**Precise statement and conditions**: P:PsiTheory; g≥1; d1+d2=3g−1; pureC(d1,d2)≤pureC(0,3g−1).

**Reference**: DGZZ SIGMA16(2020),086 §1 Eq.(6); normalized C differs by a positive (g,n)-only factor; transfer via DVV uniqueness pp.2–3

[Read the source](https://sigma-journal.com/2020/086/sigma20-086.pdf).

**Used for**: Primitive estimates and comparison anchors

</details>

<a id="input-pi-iz"></a>

<details>
<summary>7. The endpoint identity for intersections and Painlevé coefficients (PI-IZ)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-pi-iz).

**Lean declarations**:

- [WP.External.itzykson_zuber](../WPFormalization/External/Painleve.lean#L34)

**Precise statement and conditions**: P:PsiTheory, integer g≥2; pure tau2^(3g−3)=2^g(3g−3)!phi_g/((5g−5)(5g−3)); phi_g=−2^g u_g for the fixed rational zero-instanton recurrence. Classical DVV and formal-coefficient uniqueness transfer included in the deferred proof.

**Reference**: Itzykson–Zuber hep-th/9201001 p.39 Eqs.(6.7)–(6.10); GIKM arXiv:1002.3634v3 Eq.(1.3)

[Read the source](https://arxiv.org/pdf/hep-th/9201001).

**Used for**: Actual pure-psi endpoint normalization; no new all-order uniform remainder is assumed.

</details>

<a id="input-pi-leading"></a>

<details>
<summary>8. Classical large-order asymptotics of Painlevé coefficients (PI-LEADING)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-pi-leading).

**Lean declarations**:

- [WP.External.painleve_leading_error](../WPFormalization/External/Painleve.lean#L54)
- [WP.External.painleve_leading](../WPFormalization/External/Painleve.lean#L61)
- [WP.External.painleve_first_correction_error](../WPFormalization/External/AsymptoticFirstOrder.lean#L20)

**Precise statement and conditions**: The actual rational zero-instanton recurrence, A=8sqrt(3)/5 and S1=−i3^(1/4)/(2sqrt(pi)); normalizedZeroInstanton tends to1 as integer genus tends to∞. The same classical source Eq.(2.39) supplies |normalizedZeroInstanton g−1|≤C/g for all sufficiently large integer g; no order-dependent constants. Also, for the same canonical sequence and fixed first order only: |normalizedZeroInstanton g−(1−1/[8(2g−3/2)])|≤C/g² for all sufficiently large integer g. Constants do not involve WP parameters or growing truncation orders.

**Reference**: GIKM arXiv:1002.3634v3 p.2 Eqs.(1.1)–(1.5), Section2.3 Eqs.(2.35)–(2.37) and Eq.(2.39) (PDF p.12); fixed first correction: Section2.3 Eqs.(2.41)–(2.45),PDF p.13, and (1.7) at n=1

[Read the source](https://arxiv.org/pdf/1002.3634v3).

**Used for**: Leading endpoint/prefactor anchor only. Does not supply the target paper’s growing-order or compact-parameter uniformity. Actual endpoint first correction for Theorem8.1; the new WP normalization and uniform matching remain local proofs.

</details>

<a id="input-sf-gamma-ratio"></a>

<details>
<summary>9. Gamma ratio estimates with fixed parameter shifts (SF-GAMMA-RATIO)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-sf-gamma-ratio).

**Lean declarations**:

- [WP.External.gamma_ratio_error](../WPFormalization/External/SpecialFunctions.lean#L15)
- [WP.External.gamma_ratio_first_correction_error](../WPFormalization/External/AsymptoticFirstOrder.lean#L26)

**Precise statement and conditions**: For each fixed alpha,beta∈R, there exist C>0,x0>0 such that x≥x0 implies |Gamma(x+alpha)/(Gamma(x+beta)x^(alpha−beta))−1|≤C/x. No uniformity in the shifts or expansion order is assumed. First correction additionally has error C/x² after subtracting 1+(alpha−beta)(alpha+beta−1)/(2x), with constants depending on the fixed shifts only.

**Reference**: NIST DLMF5.11.13 and G0=1 in5.11.15; fixed real shifts, positive real x→∞; fixed first correction G1=(a−b)(a+b−1)/2 in5.11.15

[Read the source](https://dlmf.nist.gov/5.11.E13).

**Used for**: Finite fixed-marking endpoint prefactor conversions; not the paper’s growing-order estimates. Actual endpoint first correction, with no growing-order re-expansion admitted.

</details>

<a id="input-sf-gamma-stirling"></a>

<details>
<summary>10. Stirling remainder bounds for the real Gamma function (SF-GAMMA-STIRLING)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-sf-gamma-stirling).

**Lean declarations**:

- [WP.External.gamma_stirling_error](../WPFormalization/External/SpecialFunctions.lean#L28)

**Precise statement and conditions**: There exist fixed C,x0>0 such that all real x≥x0 satisfy |Gamma(x)/(sqrt(2pi)x^(x−1/2)exp(−x))−1|≤C/x. No growing truncation or shifts are quantified.

**Reference**: NIST DLMF5.11.3–5.11.4, g0=1 and ordinary Poincare error after the leading term

[Read the source](https://dlmf.nist.gov/5.11.E3).

**Used for**: Leading pure-psi endpoint normalization from classical Painleve input; scale3g/2g/5g Gamma products.

</details>

<a id="input-sf-binet"></a>

<details>
<summary>11. The Binet remainder and Laplace representation for log Gamma (SF-BINET)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-sf-binet).

**Lean declarations**:

- [WP.External.log_gamma_stirling_remainder](../WPFormalization/External/SpecialFunctions.lean#L45)
- [WP.External.log_gamma_ratio_laplace](../WPFormalization/External/GammaLaplace.lean#L21)

**Precise statement and conditions**: All real x>0 and integers K≥1; after summing k=1,…,K−1 the absolute log-Gamma remainder is bounded by |B_2K|/(2K(2K−1)x^(2K−1)). Exact Bernoulli factor retained; no WP quantities or truncated-order matching assumed. Also, for all real h>0,a>0: the kernel (a-(1-exp(-a*t))/(1-exp(-t)))/t is absolutely integrable after multiplication by exp(-h*t) on t>0, and its integral equals log Gamma(h+a)-log Gamma(h)-a log h. The raw value at t=0 is not claimed to be the removable value. No Taylor coefficients or growing-order estimate is admitted.

**Reference**: NIST DLMF5.11(ii), paragraph before5.11.10: positive-real logarithmic Stirling remainder bounded by first omitted term; exact shift representation is a classical integrated consequence of DLMF5.9.12 + Frullani + FTC/Fubini, not a verbatim formula

[Read the source](https://dlmf.nist.gov/5.11#ii).

**Used for**: Legitimate classical order-dependent Gamma input to endpoint estimates; paper re-expansion bounds remain new obligations. Supplies only an exact classical Gamma Laplace representation for the new local germ/Watson/Gevrey matching proof.

</details>

<a id="input-bessel-j0"></a>

<details>
<summary>12. Zeros of the Bessel J0 function (BESSEL-J0)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-bessel-j0).

**Lean declarations**:

- [WP.External.besselJ0_zeros_real](../WPFormalization/External/Bessel.lean#L14)
- [WP.External.besselJ0_positive_zero](../WPFormalization/Analysis/BesselDictionary.lean#L112)
- [WP.External.besselJ0_zero_simple](../WPFormalization/External/Bessel.lean#L19)

**Precise statement and conditions**: Standard explicitly defined J0 series: complex zero reality and simplicity of nonzero zeros are the remaining deferred generic facts. Positive-real zero existence is now PROVED from the actual a(3/2)<0 alternating bound and IVT in Analysis/BesselDictionary; its declaration has no sorry.

**Reference**: NIST DLMF10.21(i), first paragraphs: nonzero cylinder-function zeros are simple; J0 positive zero existence and all zeros real

[Read the source](https://dlmf.nist.gov/10.21#i).

**Used for**: Only J0 complex-zero reality is currently needed by the kernel positivity proof. The first-zero existence/simplicity and critical scaling limits have actual series/IVT proofs; the generic simplicity interface remains available but is not required by these core proofs.

</details>

<a id="input-gen-analytic-ift"></a>

<details>
<summary>13. Analytic implicit functions and convergence of formal branches (GEN-ANALYTIC-IFT)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-gen-analytic-ift).

**Lean declarations**:

- [WP.External.convergent_formal_implicit_solution](../WPFormalization/External/AnalyticImplicit.lean#L27)

**Precise statement and conditions**: Arbitrary signed real multivariate convergent Phi:Fin m→R[[t,v]], Phi(0)=0, det(I−D_v Phi(0)) nonzero; already given U with zero constant and the actual finite substitution fixed-point equations. Conclusion only: positive radius of absolute coefficient convergence of U. No triangularity, positivity, coefficient bound, formal construction/uniqueness or ENNReal subsolution domination is supplied.

**Reference**: Guillemin–Campbell MIT18.117 (2005), PDF pp.15–16 holomorphic inverse/implicit function theorem, pp.5–6 convergent multivariate Taylor series. The stated formal-branch convergence is a classical consequence, not a verbatim theorem.

[Read the source](https://ocw.mit.edu/courses/18-117-topics-in-several-complex-variables-spring-2005/3e8b0c3499d6226959485ace042cdaab_18117notes.pdf).

**Used for**: Only the analytic-convergence step of Lemma C.2; all paper-specific triangular construction, unique/nonnegative coefficients, geometric bound and extended-valued comparison are proved separately.

</details>

<a id="input-int-kdv"></a>

<details>
<summary>14. The first integrated KdV identity for pure psi intersections (INT-KDV)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-int-kdv).

**Lean declarations**:

- [WP.External.integrated_first_kdv](../WPFormalization/External/KdV.lean#L24)
- [WP.External.first_kdv_descendants](../WPFormalization/External/KdV.lean#L36)

**Precise statement and conditions**: P:PsiTheory; integer g≥1; arbitrary finite signed descendant list L with all entries nonnegative. (2g+len(L)−1) psi_g(0::L) equals psi_(g−1)(0^4++L)/12 plus one half of the ordered genus/subset product sum of two 0^2-marked descendants. Unstable/wrong-dimensional terms use the original zero convention. The tau1,tau0 version is proved from P.dilaton, not separately admitted.

**Reference**: Liu–Mulase–Xu, Recursions and asymptotics of intersection numbers, PDF p.3 Eq.(6); Itzykson–Zuber hep-th/9201001 Theorem2 Eq.(4.12) for classical Virasoro/DVV uniqueness transfer

[Read the source](https://www.math.ucdavis.edu/~mulase/texfiles/RecursionAsymp.pdf).

**Used for**: Only the classical pure-psi first KdV identity; the paper’s shifted normalized Eq.6.6 is proved separately by finite background splitting, exponential convolution and exact normalization. No Y, r, X, kernel, uniform estimate or new marked conclusion is admitted.

</details>

<a id="input-gen-pringsheim"></a>

<details>
<summary>15. Real-axis singularities of nonnegative power series (GEN-PRINGSHEIM)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-gen-pringsheim).

**Lean declarations**:

- [WP.External.zero_free_disk_of_nonnegative_inverseCoefficients](../WPFormalization/External/Pringsheim.lean#L26)

**Precise statement and conditions**: Arbitrary entire f:C→C, real R≥0; all inverse Taylor coefficients real and nonnegative; f(x) nonzero for all x∈[0,R]. Conclusion only f(z) nonzero for norm(z)≤R. The reciprocal pole/nearest-zero radius and Taylor-germ bridge belong to the deferred classical proof.

**Reference**: Flajolet–Sedgewick Analytic Combinatorics, Theorem IV.6, printed p.240; authors’ 2006 draft printed p.227. Generic reciprocal zero-free-disk corollary, not a verbatim theorem.

[Read the source](https://algo.inria.fr/flajolet/Publications/book.pdf).

**Used for**: Pringsheim step in proving the actual H-kernel zero-free disk. Real H positivity, coefficient hypotheses, parameter compactness, common radius and uniform bounds are proved separately; no kernel-specific estimate is admitted.

</details>

<a id="input-gen-rouche"></a>

<details>
<summary>16. Counting complex zeros with multiplicity (GEN-ROUCHE)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-gen-rouche).

**Lean declarations**:

- [WP.External.rouche_exhausts_prescribed_zeros](../WPFormalization/External/Rouche.lean#L20)

**Precise statement and conditions**: Arbitrary entire complex f,g; positive disk radius R; strict boundary difference norm(f−g)<norm(g); an arbitrary finite index type; an injective reference catalog exhausting exactly the simple g zeros inside; an equally indexed injective catalog of actual f zeros inside. Conclusion only: the target catalog exhausts all f zeros inside and they are simple. No kernel, parameter family or sign/root construction is supplied.

**Reference**: MIT18.112 Fall2008 Lecture14, Corollary1 (Rouche), PDF pp.5–6 / printed pp.4–5; prescribed-zero simplicity/exhaustion is an immediate finite-count corollary, not a verbatim statement.

[Read the source](https://ocw.mit.edu/courses/18-112-functions-of-a-complex-variable-fall-2008/59e058767d6256ca57d8e757bb257715_lecture14.pdf).

**Used for**: Classical counting step for Lemma2.1. Actual characteristic identity, boundary comparison, sine reference catalog and positive real target zeros are separately proved locally.

</details>

<a id="input-gen-hadamard"></a>

<details>
<summary>17. Product factorization of entire functions of finite order (GEN-HADAMARD)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-gen-hadamard).

**Lean declarations**:

- [WP.External.hadamard_genus_zero_of_sqrt_growth](../WPFormalization/External/Hadamard.lean#L18)

**Precise statement and conditions**: Arbitrary entire complex f with f(0) nonzero; fixed A,B>0 and actual global bound norm(f z)≤A exp(B sqrt(norm z)); an injective sequence of all and only its zeros, all simple. Conclusion only the unconditional genus0 product HasProd(1−z/root_n)=f(z)/f(0). The growth forces order≤1/2 and absolute reciprocal-zero convergence; no positivity, kernel family, root construction or uniform estimate is supplied.

**Reference**: C.McMullen, Advanced Complex Analysis, Harvard Math213a notes (2017 version), Thm3.7 printed p.43/PDF p.44; zero convergence Thm3.11 printed p.44; full proof through printed p.47. This is the order≤1/2 normalized simple-zero specialization.

[Read the source](https://people.math.harvard.edu/~ctm/home/text/class/harvard/213a/10/html/home/course/course.pdf).

**Used for**: Only the final canonical-product step of Lemma2.1, after actual K growth and the full real/simple ordered zero classification have been proved locally.

</details>

<a id="input-wp-mz-fixed"></a>

<details>
<summary>18. WP volume asymptotics with a fixed number of cusps (WP-MZ-FIXED)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-wp-mz-fixed).

**Lean declarations**:

- [WP.External.fixed_cusps_universal_leading](../WPFormalization/External/FixedCusps.lean#L19)
- [WP.External.fixed_zero_cusps_first_correction](../WPFormalization/External/FixedCuspsFirstCorrection.lean#L21)

**Precise statement and conditions**: P:PsiTheory. There exists a single unknown c>0 before quantifying n. For each fixed integer n>=0 there exist C_n>0 and a genus threshold G_n such that all integer g>=G_n satisfy |volumeModel(P,g,n)/[(2g+n-3)!(4pi^2)^(2g+n-3)/sqrt(pi*g)]-c|<=C_n/g. c=sqrt(pi)*C_MZ is not assumed equal to1. No uniformity in n or expansion order is included. The geometric-to-numerical DVV uniqueness and KMZ/Wolpert transfer is deferred, not a verified Lean consequence. The separate n=0 first-correction limit retains an unknown positive normalization c, coefficient 7/12−17/(6*pi^2); its normalization is not assumed to equal one.

**Reference**: Mirzakhani–Zograf, GAFA25(2015), Theorem1.2 and Remark1.3, arXiv1112.1151 PDFpp1–2; kappa1/WP convention PDFp4

[Read the source](https://arxiv.org/pdf/1112.1151).

**Used for**: Corollary1.2 only after the paper absolute-prefactor proof independently identifies the unknown constant from n=1. It does not supply the paper uniform all-cusp asymptotics or its canonical coefficients.; classical n=0 first correction only for Theorem11.1 sharp lower bound, not new uniform/all-order expansion

</details>

<a id="input-pi-contour"></a>

<details>
<summary>19. Contour representations and fixed-order jumps for Painlevé I (PI-CONTOUR)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-pi-contour).

**Lean declarations**:

- [WP.External.PainleveAnalytic.GIKMData](../WPFormalization/External/PainleveAnalyticData.lean#L45)
- [WP.External.PainleveAnalytic.exists_gikm_data](../WPFormalization/External/PainleveAnalyticData.lean#L184)

**Precise statement and conditions**: Normalized actual u_k with period/rotation and PI ODE at analytic points; source rational zero coefficients constrained by the complete recurrence; real one-instanton b_n constrained by original Eq1.7. Sector constants depend on angular margins and fixed N. Positive-ray jump has every fixed-m expansion with constants/threshold depending on m. The exact coefficient contour at any chosen rho>=R0 has one C_rho before all g>=1 and absolutely integrable t^(5g-2)(u1(t²)-u0(t²)); exponent follows defining Eq2.14 despite printed2.26 typo. No control of m, no actual rescaled-v identity or uniform remainder is admitted.

**Reference**: GIKM arXiv:1002.3634v3 printed pp.2,7-13 Eqs.(1.3),(1.7),(2.3)-(2.9),(2.14),(2.25),(2.29)-(2.33),(2.40)-(2.45)

[Read the source](https://arxiv.org/pdf/1002.3634v3).

**Used for**: Construct actual native PI remainder, force selected parameter zero, identify jump coefficients by local rescaling/recurrence uniqueness, then derive the new growing-order endpoint remainder.

</details>

<a id="input-pi-borel"></a>

<details>
<summary>20. The Borel representation of Painlevé I (PI-BOREL)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-pi-borel).

**Lean declarations**:

- [WP.External.PainleveAnalytic.CCHData](../WPFormalization/External/PainleveAnalyticData.lean#L145)
- [WP.External.PainleveAnalytic.exists_cch_data](../WPFormalization/External/PainleveAnalyticData.lean#L189)

**Precise statement and conditions**: One H0 analytic on the plane cut along real |s|>=1, symbolic S and local H0=S/sqrt(1-s)*alpha+beta with alpha(1)=1 on a fixed small disk. Fixed non-Stokes rays only 0<|phi|<pi/2 have their own exponential-weight L1 bound. Native PI solutions have analyticity with angular margins, the native ODE and proper-right-sector decay; their selected anti-Stokes parameter limit exists, and parameter zero gives the exact fixed off-ray Laplace sum for all sufficiently large positive xi. No numerical Stokes value, actual GIKM adapter, uniform jump/Gevrey estimate or WP object is included.

**Reference**: Costin-Costin-Huang arXiv:1310.5330v2 Theorem2, Proposition3(i),(ii), Lemma17(c),(f), printed pp.3,4,12; slit branch and fixed-ray positive-real continuation are standard monodromy/identity-principle consequences

[Read the source](https://arxiv.org/pdf/1310.5330v2).

**Used for**: Raw H finite deformation, dominated bank limits and outer exponent bounds are proved locally; apply them to actual native functions only after proving the coordinate/zero-parameter/leading adapters.

</details>

<a id="input-int-nef"></a>

<details>
<summary>21. Nef intersection inequalities and their realization on moduli spaces (INT-NEF)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-int-nef).

**Lean declarations**:

- [WP.External.classical_onepoint_nef_realization](../WPFormalization/External/NefIntersection.lean#L42)

**Precise statement and conditions**: P:PsiTheory; integer g>=2. Nonempty OnePointNefRealization P g: a classical IntersectionRealization of P, a generic nef-class intersection calculus on its genus-g one-point classes (Teissier for every pair of nef divisor classes and every interior degree), and nefness of the actual psi_1 and logarithmic kappa_1 classes. The existence proof includes DVV uniqueness/KMZ/Wolpert identification and the finite level cover/resolution, nef pullback, orbifold-to-projective common positive degree transfer. It does not assert a constructed Lean geometric instance, characteristic-zero semiampleness, a mixedJ inequality as a field, or any coefficient/ratio/asymptotic estimate.

**Reference**: Arbarello–Cornalba alg-geom/9406008 Section1 Eq.(1.5)–(1.7), PDFpp4–6; Keel math/9901149 Theorem0.4, PDFp3; Boucksom–Favre–Jonsson math/0608260v2 Theorem2.15, PDFp15. Classical DVV uniqueness and KMZ/Wolpert transfer as in INT-PSI/INT-KMZ.

[Read the source](https://arxiv.org/pdf/math/0608260).

**Used for**: The locally proved exact mixedJ-to-mixedIntegral normalization and generic Teissier client give the unchanged original C7 for all g>=1; g=1 has no interior degree and g>=2 uses this classical datum.

</details>

<a id="input-wp-mz-fixed-genus"></a>

<details>
<summary>22. Volume asymptotics at fixed genus with increasing cusp count (WP-MZ-FIXED-GENUS)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-wp-mz-fixed-genus).

**Lean declarations**:

- [WP.External.fixed_genus_normalized_volume_logarithm](../WPFormalization/External/FixedGenus.lean#L25)

**Precise statement and conditions**: P:PsiTheory and fixed g including0/1. There exist C>0 and N depending on g; all stable n>=N satisfy |log(normalizedVolume P g n)+n log(2*xCritical)|<=C log(n+1). No genus-uniform estimate, chainProfile, diagonal path, or concrete instance. Classical DVV uniqueness/KMZ/Wolpert identification transfers raw kappa integrals to P; rawV/(n!dim!) has exponential base xCritical^(-n), physical=(2pi^2)^dim rawV/dim!, normalization leaves base(2*xCritical)^(-n) and only polynomial n factors.

**Reference**: Manin–Zograf, Ann. Inst. Fourier 50 (2000), Section6 Theorem6.1 Eq.(17)–(20), printed pp528–529/PDFpp11–12.

[Read the source](https://www.numdam.org/item/10.5802/aif.1764.pdf).

**Used for**: Fixed bounded-genus branch of original Theorem1.5; growing-genus comparison and uniform gluing are paper proof obligations.

</details>

<a id="input-hyp-curves"></a>

<details>
<summary>23. Curves on hyperbolic surfaces and measurable length counts (HYP-CURVES)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-curves).

**Lean declarations**:

- [WP.External.HyperbolicCurveGeometry](../WPFormalization/External/HyperbolicCurveGeometry.lean#L22)

**Precise statement and conditions**: Same explicit G:WeilPeterssonGeometry P, its cusp Moduli and WP measure. All unoriented primitive geodesics including nonsimple; positive physical lengths; simplicity; positive-genus unique planar-side cusp labels; a finite complete catalog of every primitive length<=L; Borel cardinality counts. No supplied concrete realization, orbit integral, moment, or asymptotic. wpProbability is actual total-measure normalization with probability law proved only from finite nonzero mass.

**Reference**: Classical primitive length spectrum of finite-type finite-area cusped hyperbolic surfaces; continuous geodesic length functions on Teichmuller space and countable free homotopy classes give Borel moduli counts. Precise construction/deduction and source scope are recorded in [Source scope notes](CLASSICAL_RESULTS.md#mirzakhani). Shen–Wu2203.15681v4 Sections2.1/4.2 use these exact counts.

[Read the source](https://arxiv.org/pdf/2203.15681v4).

**Used for**: Faithful objects for the actual pants, primitive and spectral applications.

</details>

<a id="input-hyp-spectral"></a>

<details>
<summary>24. Discrete spectra and local variational estimates on pairs of pants (HYP-SPECTRAL)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-spectral).

**Lean declarations**:

- [WP.External.SpectralGeometry](../WPFormalization/External/SpectralGeometry.lean#L23)

**Precise statement and conditions**: Same G/H. Positive discrete Laplace eigenvalues counted with multiplicity, one-based j>=1, constant0 excluded; missing value represented by none; positive/ordered and measurable events. For stable(g,n), epsilon in(0,1/4), j+1 distinct two-cusp pants waists<=epsilon/6 imply jth positive eigenvalue exists<=epsilon. Single-pant field: one universal c>0, g>=2, 0<L<=1,cL<1/4, pantsCount>=1 imply lambda1 exists<=cL. No probability-one, volume ratio, or cusp-density limit.

**Reference**: Hide–Thomas arXiv2209.15568v3 Lemma5.3 PDFp26/proofp27 (all Mg,n deterministic statement); Shen–Wu arXiv2203.15681v4 Theorems7/11 and proofTheorem1 PDFpp35–36 (single-pant Cheeger cut+Buser/minmax).

[Read the source](https://arxiv.org/pdf/2209.15568v3).

**Used for**: Original1.6 vanishing spectral gap and14.3 many-small-eigenvalues deduction once actual pants/volume inputs are proved.

</details>

<a id="input-wp-shen-wu-pants"></a>

<details>
<summary>25. A second-moment lower bound for short-pants counts (WP-SHEN-WU-PANTS)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-wp-shen-wu-pants).

**Lean declarations**:

- [WP.External.ShenWuPantsBound](../WPFormalization/External/ShenWuPants.lean#L19)

**Precise statement and conditions**: Same actual G/H and normalized WP measure. Every cusp sequence with n/sqrt(g)->infinity: liminf of V(g,n−1)^2/[V(g,n)V(g,n−2)] <= liminf probability[pantsCount at L=sqrt(sqrt(g)/n)>=1]. No assumption or supplied proof that the ratio tends1, no new paper Poisson, and no eigenvalue conclusion. Finitely many unstable small-g values are immaterial to atTop.

**Reference**: Shen–Wu arXiv2203.15681v4 Proposition35 PDFp34, proofpp34–35. The stated inequality and hypotheses do not require n=o(g).

[Read the source](https://arxiv.org/pdf/2203.15681v4).

**Used for**: Published vanishing-gap mechanism; this paper must supply original1.3 uniform D-rate and pass to spectral events locally.

</details>

<a id="input-hyp-multicurve-integration"></a>

<details>
<summary>26. Cutting and integration for labeled multicurves (HYP-MULTICURVE-INTEGRATION)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-multicurve-integration).

**Lean declarations**:

- [WP.External.MulticurveTopology](../WPFormalization/External/MirzakhaniIntegration.lean#L37)
- [WP.External.MirzakhaniIntegration](../WPFormalization/External/MirzakhaniIntegration.lean#L94)

**Precise statement and conditions**: Same explicit P/G/H. Every injective simple pairwise-disjoint ordered tuple belongs to exactly one finite orbit family. Actual cut genera/cusp labels/edge-side incidences are stable, connected, satisfy Euler characteristic, classify and realize the orbits, and their planar sides agree with H.planarSide in positive genus. One-handle count M is computed from cut-side topology; orientation index is computed from realizable edge flips. Outside (g,n)=(1,1),(2,0), each measurable nonnegative orbit test has WP integral coefficient (2^M*index)^(-1) times actual G cut-volume product and product x_j dx_j. No pants label count, moment, asymptotic, or concrete geometric instance supplied.

**Reference**: Shen–Wu arXiv2203.15681v4 Section2.2 Theorem6 and Remark, PDFp7; classical change-of-coordinates classification and gluing of labeled surfaces. Hide–Thomas arXiv2209.15568v3 Remark3.2 and following cut classification illustrate the genus-zero case. Exact full interface review: [Source scope notes](CLASSICAL_RESULTS.md#mirzakhani).

[Read the source](https://arxiv.org/pdf/2203.15681v4).

**Used for**: Locally prove actual pants star-cut classification, label enumeration and factorial-moment formulas, then concentration/Poisson; generic cut data can also support primitive-count applications.

</details>

<a id="input-wp-sw-critical-volume"></a>

<details>
<summary>27. General upper bounds and critical-range lower bounds for WP volumes (WP-SW-CRITICAL-VOLUME)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-wp-sw-critical-volume).

**Lean declarations**:

- [WP.External.shenWu_volume_upper](../WPFormalization/External/CriticalVolumeBounds.lean#L25)
- [WP.External.shenWu_volume_critical_lower](../WPFormalization/External/CriticalVolumeBounds.lean#L33)

**Precise statement and conditions**: P:PsiTheory. Upper: one C>0 for every stable(a,b), V<=C*(4pi^2)^(h-1)*Gamma(h)/sqrt(h), h=2a-2+b. Lower: for each fixed A>0, one c_A>0 and G_A, all g>=G_A and all n<=A sqrt(g), c_A*(4pi^2)^(h-1)*Gamma(h)/sqrt(h)<=V(g,n). Classical DVV uniqueness/KMZ/Wolpert transfer to arbitrary P is deferred. No graph, cut count, allocation, new error rate or growing-A statement.

**Reference**: Shen–Wu arXiv2203.15681v4 Lemmas18/19, printedpp12–13. The fixed-A uniform consequence follows from the finite-product proof of Lemma19. Lemma18 h>=2 extends to the two stable h=1 types by finite enlargement.

[Read the source](https://arxiv.org/pdf/2203.15681v4).

**Used for**: Only classical volume envelopes in AppendixG; actual Gamma convolution, cusp mass, allocation and geometric cut counts remain local paper proofs.

</details>

<a id="input-hyp-collar"></a>

<details>
<summary>28. Simplicity and disjointness of short primitive geodesics (HYP-COLLAR)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-collar).

**Lean declarations**:

- [WP.External.CollarGeometry](../WPFormalization/External/CollarGeometry.lean#L20)

**Precise statement and conditions**: Same G/H/T actual primitive family and disjointness relation. Primitive length strictly<2arsinh(1) implies simple. Two distinct simple primitives both strictly below this threshold are T.disjoint. No pants topology, factorial moment, concentration, Poisson or systole limit.

**Reference**: Buser, Geometry and Spectra of Compact Riemann Surfaces, Theorems4.4.6 (short primitive is simple) and4.1.6 (short distinct simple curves disjoint). Hide–Thomas arXiv2209.15568v3 printedpp1/8 explicitly use these two facts for finite-area cusped surfaces.

[Read the source](https://arxiv.org/pdf/2209.15568v3).

**Used for**: Pass short actual primitive tuples to generic ordered-disjoint-simple integration; paper topology and moment work is proved separately.

</details>

<a id="input-tight-bz"></a>

<details>
<summary>29. Tight-boundary geometry and the moment transform (TIGHT-BZ)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-tight-bz).

**Lean declarations**:

- [WP.External.ProtectedCycleGeometry](../WPFormalization/External/TightMoments.lean#L33)
- [WP.External.TightRegions](../WPFormalization/External/TightMoments.lean#L61)
- [WP.External.BuddZonneveldTransform](../WPFormalization/External/TightMoments.lean#L96)

**Precise statement and conditions**: Same actual G.Moduli/wpMeasure. Unoriented unparametrized simple geometric cycles include distinct protected boundary cycles with their exact physical lengths and the zero-length cusp boundary convention. Capping fills precisely unprotected boundaries; tightLocus is DEFINED by each protected boundary being the unique simple cycle in its capped free-homotopy class of length<=that boundary length. Regions supply its measurability. Transform: every stable protected(g,p), nonnegative physical L, finite nonnegative weight mu supported in[0,B], every analytic root germ R(0)=0 satisfying Zmu(R(t),t)=0 near0; the weighted actual restricted-volume coefficient is the Taylor coefficient of the generic finite complex moment polynomial. Zmu=X(2pi²r)/(2pi²)-t integral I0(L sqrt(2r))dmu; Mj=partial_r^(j+1)Zmu at R(t). Only coefficientwise equality, no global real convergence, paper Y-specialization, shifted amplitude identity, uniform error or spectrum conclusion supplied.

**Reference**: Budd–Zonneveld arXiv2307.04708 (11July2023), Section1.2 Eq.(7)–(8), root Eq.(21), moments Eq.(23), Proposition12 Eq.(69)–(70), descendant series Eq.(65) and times Eq.(68), followed by classical dilaton resummation. Full review [Source scope notes](CLASSICAL_RESULTS.md#tight-transform).

[Read the source](https://arxiv.org/pdf/2307.04708).

**Used for**: Prove cusp-weight specialization, full analytic generating-series convergence, exact normalization in paperF1, and F2/F3 locally, then tight spectrum applications.

</details>

<a id="input-int-higher-kappa"></a>

<details>
<summary>30. Higher logarithmic kappa intersections (INT-HIGHER-KAPPA)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-int-higher-kappa).

**Lean declarations**:

- [WP.External.HigherKappaRealization](../WPFormalization/External/HigherKappa.lean#L73)

**Precise statement and conditions**: Same explicit PsiTheory P and IntersectionRealization R; higher logarithmic kappa_j=pi_*(c1(omega_pi(sum sections))^(j+1)), kappa1 exactly R.classes.kappa1. All stable (g,n), all finite nonnegative multiplicities of weighted top degree: mixed integral >=0; kappa1 top integral >0. For every g>=2 and every complex times s_j, the finite descendant polynomial at p_j=[z^j](1-exp(-sum_{i>=1}s_i z^i)) equals the finite higher-kappa polynomial with standard multiplicity factorials. p0=0; no analytic/growing-parameter premise or tight/Y field.

**Reference**: Manin–Zograf, Ann.Inst.Fourier50(2000) Thm4.1 printed525 (arbitrary-times Schur transform); Arbarello–Cornalba alg-geom/9406008 eq(1.6) printed5 (kappa1 ample); Keel Ann.Math149(1999) Thm0.4 printed255 (universal log-dualizing nef in char0); Lazarsfeld Positivity I Ex1.4.16 pp57–58 (mixed nef intersections). Mixed higher-kappa nonnegativity is the explicit classical fiber-power/projection-formula corollary, independently checked, not a direct statement attributed to KMZ.

[Read the source](https://www.numdam.org/item/AIF_2000__50_2_519_0.pdf).

**Used for**: Local proof of unmarked (p=0) positive tight factor through actual ordinary moment kernel, inverse/log jets and specialization; general classical input only.

</details>

<a id="input-hyp-tight-curves"></a>

<details>
<summary>31. Homotopy classes of closed geodesics after capping (HYP-TIGHT-CURVES)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-tight-curves).

**Lean declarations**:

- [WP.External.TightGeodesicGeometry](../WPFormalization/External/TightGeodesicGeometry.lean#L38)

**Precise statement and conditions**: Same G/T/H. Primitive and simple are separate, positive geometric length, complete finite short catalog. cap lands in existing T.cycles.CappedClass. IsTight is DEFINED as non-null capped class plus unique length minimizer among all closed geodesics. cuspPrimitiveEquiv preserves length/simple and identifies the actual H.Primitive; no simplicity condition is inserted into full tight counts.

**Reference**: Budd–Lions arXiv2506.02611v3 §§1/3, Proposition3.1 pp12–13. All unoriented closed geodesics, primitive/simple predicates, filled homotopy classes, finite short spectrum and identification with the same cusped H family.

[Read the source](https://arxiv.org/pdf/2506.02611v3).

**Used for**: Actual primitive tight spectrum and local F4 tuple/count proofs, not a probability or asymptotic input.

</details>

<a id="input-tight-cut-topology"></a>

<details>
<summary>32. Orbit classification of ordered tight multicurves (TIGHT-CUT-TOPOLOGY)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-tight-cut-topology).

**Lean declarations**:

- [WP.External.TightMulticurveTopology](../WPFormalization/External/TightMulticurveTopology.lean#L19)

**Precise statement and conditions**: Same G/T/H/Q capped homotopy and good tuple definition. Finite ordered MCG orbit types on the filled base (g,p); free boundaries are absent from cut graph and later explicitly assigned. For Stable(g,p), every proper primitive simple pairwise disjoint tight tuple occupies exactly one orbit. Actual MulticurveCutData preserves labeled protected boundaries/ordered edges, stable components, Euler relation, connected incidence and cut-isomorphism classification. For Stable(g,p), every exact labeled cut datum with stable components, connected incidence and Euler genus budget is realized by an existing A.Orbit up to full cut isomorphism, preserving protected labels, ordered edges, loops and edge-side flips. This generic cut_realizes supplies no free-cusp allocations or estimate.

**Reference**: Budd–Lions arXiv2506.02611v3 §3 pp12–17; ordinary classification of labeled oriented-surface multicurves with ordered edges. Stable filled base restriction retained. Generic cut_realizes additionally uses the same oriented-surface cut classification underlying Prop3.2 and its one-component orbit example; parent checked exact Stable/connected/Euler typed proposal.

[Read the source](https://arxiv.org/pdf/2506.02611v3).

**Used for**: Exact tight integration and locally proved connected/separating configuration sums.

</details>

<a id="input-bl-tight-integration"></a>

<details>
<summary>33. Integration over restricted regions for tight multicurves (BL-TIGHT-INTEGRATION)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-bl-tight-integration).

**Lean declarations**:

- [WP.External.BuddLionsTightIntegration](../WPFormalization/External/BuddLionsTightIntegration.lean#L19)

**Precise statement and conditions**: Same actual G.wpMeasure, T.region and T.tightVolume; stable filled(g,p), nonnegative protected/free physical lengths. Every ordered orbit and measurable nonnegative test: restricted orbit integral equals its positive coefficient times physical orthant length integral of the actual finite sum over all assignments of labeled free boundaries to cut vertices, product tightVolumes, and product edge lengths. Connected complement coefficient exactly2^-r; all coefficients<=1. Includes classical measurability; no F2/F3, coefficient extraction or spectrum estimate.

**Reference**: Budd–Lions arXiv2506.02611v3 Proposition3.2 pp13–17. The exact formula includes all labeled free-boundary assignments, coefficient<=1 and connected coefficient2^(-r).

[Read the source](https://arxiv.org/pdf/2506.02611v3).

**Used for**: Locally proved AppendixF separating/connected moment formulas and Theorem14.4.

</details>

<a id="input-bl-tight-geometry"></a>

<details>
<summary>34. Extension and general-position properties of tight geodesic families (BL-TIGHT-GEOMETRY)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-bl-tight-geometry).

**Lean declarations**:

- [WP.External.BuddLionsTightGeometry](../WPFormalization/External/BuddLionsTightGeometry.lean#L23)

**Precise statement and conditions**: Same actual all-geodesic Q and tight orbit A, cusp surface X, g>=2 where specified. NoSimpleLengthTies required pointwise and separately WP-a.e. Short primitive tight<=b implies some simple primitive tight<=b. No-short extension at scale s>0,epsilon>0,B>0 requires 2B(r+2)/epsilon+2<g; a short nonsimple or intersecting primitive tight pair extends a good ordered r-tuple to separating r+m with m<=2B(r+2)/epsilon and each length<=sB(r+2). Short-systole branch requires0<epsilon<a<=B and original lengths in[sa,sB]; appends a new short curve or <=3 separator curves of lengths<=s(2B+epsilon). Both retain original tuple as exact ordered prefix. No probability estimate, limiting moment, or prescribed-cusp asymptotic field.

**Reference**: Budd–Lions arXiv2506.02611v3 Proposition3.1/Lemma3.3 pp12–16 and deterministic constructions in proofs of Propositions5.2–5.3 pp37–41, especially eqs60–61; shortest tight curve simple as used on p40. Near-critical Boltzmann probability conclusions are excluded.

[Read the source](https://arxiv.org/pdf/2506.02611v3).

**Used for**: Local deterministic count injections, negligible bad-event moment bounds and genuine full tight primitive process in14.4.

</details>

<a id="input-prob-point-borel"></a>

<details>
<summary>35. The measurable structure on point-measure spaces (PROB-POINT-BOREL)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-prob-point-borel).

**Lean declarations**:

- [WP.External.pointMeasure_count_measurable](../WPFormalization/External/PointProcessProbability.lean#L28)
- [WP.External.pointMeasure_nnreal_aemeasurable_of_prefix_counts](../WPFormalization/External/PointProcessProbability.lean#L37)
- [WP.External.pointMeasure_aemeasurable_of_basis_counts](../WPFormalization/External/PointProcessProbability.lean#L78)

**Precise statement and conditions**: E locally compact second countable Hausdorff Borel. Actual PointMeasure is locally finite Regular measure, integer on relatively compact Borel sets; actual vague topology is induced by all C_c real integrals, with its Borel sigma algebra. Count evaluation for any relatively compact Borel window is Measurable. On NNReal all actual prefix[0,b] counts AEMeasurable imply actual process AEMeasurable, including0. General basis is countable relatively compact Borel semiring with local finite-union approximation K subset interior(W) subset W subset U, and intensity-continuity; all basis counts AEMeasurable imply process AEMeasurable for an arbitrary source measure.

**Reference**: Kallenberg Foundations of Modern Probability2ed(2002) A2.3(iv),p564, vague-Borel integral/count generators. Prefix and countable-window AEMeasurable forms are explicitly derived classical corollaries, not literal source statements. Independently reviewed [Source scope notes](CLASSICAL_RESULTS.md#point-process).

[Read the source](https://doi.org/10.1007/978-1-4757-4015-8_16).

**Used for**: Only measurable encoding of locally constructed actual geometric Dirac sums, full tight counts and marked spectra.

</details>

<a id="input-prob-factorial-pos"></a>

<details>
<summary>36. A factorial-moment criterion for Poisson limits with positive rates (PROB-FACTORIAL-POS)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-prob-factorial-pos).

**Lean declarations**:

- [WP.External.factorial_moments_poisson_positive](../WPFormalization/External/PointProcessProbability.lean#L49)

**Precise statement and conditions**: Every finite dimension, varying measurable probability spaces (eventually probability) and eventually AEMeasurable Nat-valued count vectors. Strictly positive finite NNReal rates. Every mixed multiindex factorial moment, includingzero, is an actual ENNReal lintegral tending to the finite product rate powers. Conclusion: actual vector laws converge against all bounded continuous tests to the explicit product of Mathlib poissonMeasure rates.

**Reference**: Hide–Thomas arXiv2209.15568v3 Proposition3.1,p7, checked primary text independently. Eventual probability/AEMeasurable formulation is the cofinal-shift and measurable-representative corollary.

[Read the source](https://arxiv.org/pdf/2209.15568v3).

**Used for**: Poisson identification only after local actual mixed factorial moments have been proved; no geometric moment/tail assumption is supplied.

</details>

<a id="input-prob-factorial-zero"></a>

<details>
<summary>37. Extending the factorial-moment criterion to zero rates (PROB-FACTORIAL-ZERO)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-prob-factorial-zero).

**Lean declarations**:

- [WP.External.factorial_moments_poisson_nonneg](../WPFormalization/External/PointProcessProbability.lean#L63)

**Precise statement and conditions**: Same varying/eventually probability, eventually AEMeasurable Nat vectors and all ENNReal mixed factorial moments; rates may be zero, empty finite vector allowed. Target is exact productPoissonMeasure, including deterministiczero coordinates.

**Reference**: Explicit derived classical corollary of Hide–Thomas Proposition3.1 plus ordinary Markov inequality and finite union bound: discard zero-rate coordinates via first factorial moments, apply positive-rate theorem, reinsert deterministiczero. Not attributed as literal positive-rate proposition.

[Read the source](https://arxiv.org/pdf/2209.15568v3).

**Used for**: Generic Poisson count identification on zero-width/zero-intensity windows, after local moment proof.

</details>

<a id="input-prob-ppp-exists"></a>

<details>
<summary>38. Existence of Poisson random point measures (PROB-PPP-EXISTS)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-prob-ppp-exists).

**Lean declarations**:

- [WP.External.poisson_point_process_exists](../WPFormalization/External/PointProcessProbability.lean#L90)

**Precise statement and conditions**: E lcsc Hausdorff Borel; intensity nu locally finite Regular, hence finite on compacts and sigma-finite. Exists actual ProbabilityMeasure on genuine PointMeasure E with exact joint count law equal to independent Poisson on every finite pairwise disjoint relatively compact Borel family. Intensity may have atoms, multiplicities allowed. No target convergence is asserted.

**Reference**: Last–Penrose Lectures on the Poisson Process, author manuscript21Aug2017, Theorem3.6,p21 and proof/Cor3.7. lcscH locally finite Radon encoding uses countable compact exhaustion and modification on one null set. Independently downloaded complete primary author PDF and checked theorem/proof.

[Read the source](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf).

**Used for**: Target laws for all locally constructed geometric processes; intensity formulas must be proved locally.

</details>

<a id="input-prob-vague-counts"></a>

<details>
<summary>39. Point-process convergence from window-count distributions (PROB-VAGUE-COUNTS)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-prob-vague-counts).

**Lean declarations**:

- [WP.External.pointMeasure_vague_of_count_vectors](../WPFormalization/External/PointProcessProbability.lean#L98)
- [WP.External.pointMeasure_vague_of_semiring_mixed_factorials](../WPFormalization/External/PointProcessProbability.lean#L117)
- [WP.External.pointMeasure_vague_of_semiring_count_laws](../WPFormalization/External/PointProcessProbability.lean#L140)

**Precise statement and conditions**: E lcscH Borel, actual pointmeasure random variables eventually AEMeasurable under eventually probability measures; target actual pointmeasure probability law. Full-count version quantifies every finite relatively compact Borel family and requires each target boundary mass a.s.zero before joint count-law convergence. Semiring version: locally finite Regular intensity, countable continuity semiring with finite-union approximation leaving internal margin K subset interior(W) subset W subset U; all finite disjoint basis windows and all mixed factorial orders tend to actual intensity powers; target exactPPP law. Conclusion is genuine vague bounded-continuous law convergence. No simplicity/diffuse or geometric/tail field. Count-law semiring version replaces all mixed factorial moment premises by actual joint count-law convergence for every finite disjoint basis-window family to the corresponding product Poisson law. ContinuityWindowBasis includes empty set, finite disjoint differences and compact/open finite-union approximation with interior margin. Includes d=0 and zero rates; no first-moment, diffuse or simple-process premise.

**Reference**: Kallenberg2ed(2002) Theorem16.16(iii)=> (i),pp316–317, with Lemma16.15 and A2.3. Semiring+mixed factorial version is an explicitly derived generic corollary of local first-moment tightness, finite disjointification and C_c approximation plus the factorial criterion; independently reviewed, not a literal theorem attribution. New count-law semiring version: Kallenberg2ed Ch16 Exercise11 printed327 extends 16.16(iii) to separating classes; finite semiring disjointification and finite unions give the explicitly derived count-law corollary, without moment assumptions.

[Read the source](https://doi.org/10.1007/978-1-4757-4015-8_16).

**Used for**: Generic topology transfer after all local geometric counts, moments, compact mass control and marked-tail work are supplied.

</details>

<a id="input-mc-count-borel"></a>

<details>
<summary>40. Measurability of unordered multicurve observables (MC-COUNT-BOREL)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-mc-count-borel).

**Lean declarations**:

- [WP.External.MulticurveCountingMeasurability](../WPFormalization/External/MulticurveCountingMeasurability.lean#L28)

**Precise statement and conditions**: Same actual G/H/T. Arbitrary finite family of ordered MCG multicurve orbits s, arbitrary relatively compact Borel edge-length vector window B. The genuine unordered count is DEFINED as ENNReal tsum1 over finite subsets of actual H.Primitive admitting an ordering gamma with orbit in s and length vector in B. It is Measurable on actual G.Moduli. No graph selection, genus/cusp asymptotic, uniform constant, upper bound or paper limit is a field; infinity is retained rather than Nat.card infinite=0.

**Reference**: Classical marked-curve countability, Fenchel–Nielsen continuity and MCG-quotient measurable descent in Mirzakhani Simple geodesics and WP volumes, Invent.Math167(2007). Checked primary12July2005 author version §2 pp8–12 (FN chart/cut/symmetry) and §8 pp36–43 (moduli covering/unfolding); published version integration section is §7. This generic measurability statement is an explicit elementary corollary of that setup, not a newly attributed counting estimate. Different-version volume conventions are irrelevant to this measurable-only corollary.

[Read the source](https://www.math.stonybrook.edu/~mlyubich/Archive/Geometry/Teichmuller%20Space/Mirz3.pdf).

**Used for**: Actual unordered cut-count measurability and genuine expectation interpretation of G1, after locally proved subtype equivalence and unordered-to-ordered injection.

</details>

<a id="input-hyp-tight-borel"></a>

<details>
<summary>41. Countable geodesic labels and measurable moduli quotients (HYP-TIGHT-BOREL)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-tight-borel).

**Lean declarations**:

- [WP.External.TightGeodesicBorelModel](../WPFormalization/External/TightGeodesicBorelModel.lean#L17)

**Precise statement and conditions**: Fixed g>=2,n and same actual G/T/H/Q. A marked measurable surface space forgets surjectively and measurably to the actual cusped TightSurface; measurable subsets descend from their pullback. A fixed countable label set is pointwise equivalent to all Q.Geodesic, including nonsimple classes and powers. Primitive/simple/capped-null/capped-class equality/disjoint predicates are fixed topological label relations tied to actual Q by iff. Each actual Q.length label function is Borel. No tight-minimizer predicate, full count, bad event measurability or asymptotic is a field.

**Reference**: Wolpert Behavior of geodesic-length functions, arXivmath0701556v4 §2.3 printed14 (all nonperipheral free-homotopy/holonomy length), §4.1 pp35–36 (real analytic FN charts); Budd–Lions arXiv2506.02611v3 §3 pp14–16 marked/moduli quotient and fixed capped homotopy. Borel descent is the classical countable proper MCG/orbifold quotient corollary, not a paper tight-count theorem.

[Read the source](https://arxiv.org/pdf/math/0701556v4).

**Used for**: Local proofs of actual IsTight predicates, primitive tight window counts and bad-intersection event measurability for14.4.

</details>

<a id="input-hyp-surface-quotient"></a>

<details>
<summary>42. Hyperbolic quotient surfaces and primitive geodesics (HYP-SURFACE-QUOTIENT)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-surface-quotient).

**Lean declarations**:

- [WP.External.HyperbolicPacking.QuotientSurface](../WPFormalization/External/HyperbolicSurfacePacking.lean#L55)
- [WP.External.HyperbolicPacking.PrimitiveAxis](../WPFormalization/External/HyperbolicSurfacePacking.lean#L40)
- [WP.External.HyperbolicPacking.PrimitiveGeometry](../WPFormalization/External/HyperbolicSurfacePacking.lean#L91)
- [WP.External.HyperbolicPacking.BorderedGeometry](../WPFormalization/External/HyperbolicSurfacePacking.lean#L143)
- [WP.External.HyperbolicPacking.AmbientRealization](../WPFormalization/External/HyperbolicSurfacePacking.lean#L177)

**Precise statement and conditions**: Actual Mathlib upper-half-plane metric and invariant area, free proper orientation-preserving deck group, closed convex lift with complete geodesic boundary, actual quotient metric/fibers/local area. Primitive classes are complete axial conjugacy-or-inverse classes with actual period and trace. Finite catalog below every fixed length has no uniform cardinal bound. Intrinsic compact geodesic boundary circles and finite-area cusp ends; area=2pi*(-chi). AmbientRealization identifies the same actual H primitive lengths/topology; no instance is constructed.

**Reference**: Martelli Hyperbolic geometry, surfaces and 3-manifolds (18Dec2013), Ch3 Thm1.13/Cor1.14 p52 convex universal lifts, Ch4 Prop1.1 p69 injectivity radius and Prop1.14 p72 geodesic/axis classes; Ch5 Thm1.3 p84 compact Gauss-Bonnet. Finite-area cusp Gauss-Bonnet is explicitly derived by horocycle truncation using Ch4 Prop1.7 p71 (omitted cusp area equals horocycle length), not attributed as literal compact theorem. Primary full PDF independently checked; per-field ledger [Source scope notes](CLASSICAL_RESULTS.md#hyperbolic-packing).

[Read the source](https://web.dm.unipi.it/martelli/didattica/matematica/2014/Hyperbolic%20geometry.pdf).

**Used for**: G2 locally proved net/loop packing and bounded primitive count; later actual intrinsic filled-piece and ambient inclusion bridges remain separate obligations.

</details>

<a id="input-hyp-local-packing"></a>

<details>
<summary>43. Local geometry of hyperbolic disks and thin collars (HYP-LOCAL-PACKING)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-local-packing).

**Lean declarations**:

- [WP.External.HyperbolicPacking.PackingClassics](../WPFormalization/External/HyperbolicSurfacePacking.lean#L120)

**Precise statement and conditions**: Complete boundaryless finite-area actual quotient, epsilon=1/4. Exact plane disk area2pi(cosh r-1), embedded disks at epsilon-thick points, every primitive outside the short-core catalog meets thick part, Borel pairwise disjoint standard collars of cores with length<2epsilon, exact collar area2ell/sinh(ell/2). No net size, loop count, short primitive cardinal bound or dependence on growing genus/cusps is a field.

**Reference**: Martelli Ch2 Prop4.1 p45 polar metric and Ch4 Prop1.1 p69; Parlier Interrogating surface length spectra, author7Nov2016 pp4-6 Lemmas2.1-2.4 (closed case); Hide arXiv2107.14555v4 Lemma4.7 proof Section4.4 p19 explicitly adapts the local collar/thin argument to cusps via Buser4.4.6. Collar area is derived by integrating the standard cosh(t) collar metric; no final asymptotic bound from Hide is admitted. Quantitative epsilon=1/4 cutoff supplement: Calegari scl authorPDF printedp52 Thm3.1/Rem3.2, 2D torsion-free displacement bound>=arsinh(1)>1/2. See independent source/type review.

[Read the source](https://arxiv.org/pdf/2107.14555v4).

**Used for**: G2 net existence/area-packing/based-loop encoding/cardinality all proved locally from these local classical facts.

</details>

<a id="input-hyp-doubling"></a>

<details>
<summary>44. Doubling surfaces along geodesic boundaries (HYP-DOUBLING)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-doubling).

**Lean declarations**:

- [WP.External.HyperbolicPacking.DoublingClassics](../WPFormalization/External/HyperbolicSurfacePacking.lean#L158)

**Precise statement and conditions**: Finite-area intrinsic hyperbolic surface with compact geodesic boundary circles and cusp ends. A complete boundaryless quotient with local PackingClassics, actual injective local isometric point inclusion and injective primitive inclusion preserving length and trace, complete area<=2 intrinsic area. No uniform primitive count or filled-piece classification is assumed.

**Reference**: Martelli Ch3 Prop1.15 p53 hyperbolic gluing and Ch4 Prop2.20 p81 proof of doubling compact geodesic boundary while retaining finite-volume cusps. Root-closed primitive inclusion is the explicit unique-axis corollary: a root has the same geodesic image and already closes in the embedded intrinsic piece. Empty-boundary identity avoids using a disconnected double as a connected quotient.

[Read the source](https://web.dm.unipi.it/martelli/didattica/matematica/2014/Hyperbolic%20geometry.pdf).

**Used for**: G2 transfers the locally proved complete-surface count to intrinsic bordered surfaces uniformly before all metrics.

</details>

<a id="input-mc-cut-restriction"></a>

<details>
<summary>45. Compatibility of multicurve cutting with restriction (MC-CUT-RESTRICTION)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-mc-cut-restriction).

**Lean declarations**:

- [WP.External.MulticurveRestrictionGeometry](../WPFormalization/External/MulticurveRestrictionGeometry.lean#L55)

**Precise statement and conditions**: Same actual G/H/T, any injection Fin q into Fin r, actual orbit restriction preserves membership of the selected ordered primitive tuple. Gluing all deleted edges gives a surjection of vertices, preserves cusp labels/retained edge sides up to flips, joins precisely connected deleted-edge fibers, and genus satisfies Euler gluing including loops. Empty restriction and full reordering retained. No primitive nonseparating/pants classification, expectation, uniform bound, G3 recording or G4 limit is a field.

**Reference**: Mirzakhani Simple geodesics and Weil-Petersson volumes, primary12July2005 author version Section2 printed11-12 (remove disjoint annular neighborhoods, preserve original cusp labels and both new sides), Section8 printed36-38 ordered MCG multicurve covers. Restriction/reordering is the naturality of that literal surface-cut construction. The fiber Euler identity is an explicitly derived orientable-surface gluing corollary, not attributed as a verbatim finite-graph formula in the source.

[Read the source](https://www.math.stonybrook.edu/~mlyubich/Archive/Geometry/Teichmuller%20Space/Mirz3.pdf).

**Used for**: Local proof relating one-curve cuts to full ordered multicurve cut graphs for actual mixed nonseparating/pants counts; reindexing coherence.

</details>

<a id="input-hyp-arc-endpoint"></a>

<details>
<summary>46. Local comparison of geodesic arc endpoints (HYP-ARC-ENDPOINT)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-arc-endpoint).

**Lean declarations**:

- [WP.External.ShortFillingGeometry.SegmentClassics](../WPFormalization/External/ShortFillingGeometry.lean#L29)

**Precise statement and conditions**: Actual quotient/primitive axes B; distinct simple closed geodesics, positive upper length L for both, distinct parameter points in each one-period interval representing the same two endpoints. Their arc lengths satisfy 2log(coth(L/4))<=|delta s|+|delta t|. No intersection cardinality, total graph size, network recording or expectation field.

**Reference**: Mirzakhani–Petri Lengths of closed geodesics on random surfaces of large genus, author RandSurf.pdf, printedp15 Lemma4.4 (Basmajian Lemma2.2) and local portion of Prop4.5 proof pp15-16. The proof explicitly treats simple geodesics as well. Only the universal-cover local endpoint inequality is licensed; applicability to cusps is a local corollary, not the published closed-surface expectation theorem.

[Read the source](https://webusers.imj-prg.fr/~bram.petri/RandSurf.pdf).

**Used for**: G3 actual finite intersection set and finite parameter-grid injection are proved locally from this local comparison.

</details>

<a id="input-hyp-intrinsic-pieces"></a>

<details>
<summary>47. Intrinsic completions of subsurfaces and primitive curves (HYP-INTRINSIC-PIECES)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-intrinsic-pieces).

**Lean declarations**:

- [WP.External.ShortFillingGeometry.BoundaryRealization](../WPFormalization/External/ShortFillingGeometry.lean#L43)
- [WP.External.ShortFillingGeometry.IntrinsicPiece](../WPFormalization/External/ShortFillingGeometry.lean#L56)
- [WP.External.ShortFillingGeometry.AmbientCurveCompatibility](../WPFormalization/External/ShortFillingGeometry.lean#L95)
- [WP.External.ShortIntrinsicRegionGeometry.IntrinsicRegionData](../WPFormalization/External/ShortIntrinsicRegionGeometry.lean#L19)
- [WP.External.ShortIntrinsicBoundaryGeometry.IntrinsicBoundaryData](../WPFormalization/External/ShortIntrinsicBoundaryGeometry.lean#L15)

**Precise statement and conditions**: Intrinsic finite-area geodesic-boundary completion and actual quotient, exact intrinsic frontier boundary circles, local isometric ambient map injective only on open interior, actual primitive projection preserving length and axis at every parameter, closed ambient interior geodesics lift intrinsically. Formal boundary classes may have the same ambient image; no all-primitive projection injectivity. Actual cusped H ambient has complete lift domain; H.simple and T.disjoint equal actual trace meanings. Independent IntrinsicRegionData for the SAME actual P says frontier(actual interior image)=union projected actual formal boundary traces and ambient area(image)=intrinsic area(univ). IntrinsicBoundaryData only says distinct projected formal boundary primitives have disjoint ambient traces; duplicate projected sides are allowed. Actual S/cut creators carry companions; no instance is asserted for arbitrary partial IntrinsicPiece.

**Reference**: Martelli18Dec2013 Ch3 Def1.12/Thm1.13/Cor1.14 pp52–53 actual convex/geodesic-boundary completion and half-disk charts, Riemannian volume-form definition p11; Ch4 Prop2.20 pp80–81 actual cusp compactification. Hide arXiv2107.14555v4 Def4.10/4.12 pp22–23 retains duplicate intrinsic boundary sides. Farb–Margalit Cor1.9 p34 straightening/minimal position. Additional frontier/area/disjoint companions are explicitly derived ordinary actual-subsurface semantics, not verbatim theorem records.

[Read the source](https://arxiv.org/pdf/2107.14555).

**Used for**: G3 chooses intrinsic lifts of original ambient curves, derives the finite-choice injection from G2 locally; canonical filling, cut recording and graph classification remain new obligations.

</details>

<a id="input-hyp-single-filling"></a>

<details>
<summary>48. The filling subsurface of one nonsimple geodesic (HYP-SINGLE-FILLING)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-single-filling).

**Lean declarations**:

- [WP.External.ShortFillingGeometry.SingleCurvePieceData](../WPFormalization/External/ShortFillingGeometry.lean#L80)
- [WP.External.ShortFillingGeometry.SingleCurvePieceClassics](../WPFormalization/External/ShortFillingGeometry.lean#L87)
- [WP.External.ShortSingleCurveFillingGeometry.SingleCurveFillingClassics](../WPFormalization/External/ShortSingleCurveFillingGeometry.lean#L33)
- [WP.External.ShortBorderedSingleCurveGeometry.BorderedSingleCurveBoundaryClassics](../WPFormalization/External/ShortBorderedSingleCurveGeometry.lean#L36)
- [WP.External.ShortSingleCurveMinimalityGeometry.SingleCurveMinimalityClassics](../WPFormalization/External/ShortSingleCurveMinimalityGeometry.lean#L18)
- [WP.External.ShortActualCutRealizationGeometry.SingleCurveCutCompanionData](../WPFormalization/External/ShortActualCutRealizationGeometry.lean#L45)
- [WP.External.ShortFullFillingGeometry.FullSingleCurveFillingClassics](../WPFormalization/External/ShortFullFillingGeometry.lean#L49)
- [WP.External.ShortFullFillingGeometry.FullSingleCurveFillingClassics.fills](../WPFormalization/External/ShortFullFillingGeometry.lean#L49)

**Precise statement and conditions**: Actual Stable(g,n), X:G.Moduli g n 0, genuinely nonsimple ambient H primitive, same A. Existing S.piece provides actual intrinsic containing piece and two numeric bounds. Refined SingleCurveFillingClassics A hcomplete S explicitly requires every actual ambient domain=univ, refers to SAME S choice, and gives an actual intrinsic primitive beta projecting gamma with trace in actual interior, such that every actual simple positive-homotopy-length interior loop disjoint from beta is UFH one actual formal boundary. This InteriorFilling is a precise local consequence, not an asserted definition equivalent to the full complementary-region topology. No claim for arbitrary S instance; phase2 must choose the actual Hide construction. Same actual finite-area geodesic-boundary B with actual boundary realization R; nonsimple primitive whose actual trace is in actual intrinsicInterior. RN/perimeter/fill-and-straighten within its actual closed convex lift gives genuine IntrinsicPiece with contains/inside/exact actualfrontier and boundaryLength≤2ell. Duplicate formal sides retained. No positiveboundary, pants, waist, kernel support or probability field; those local consequences are proved separately. SingleCurveMinimalityClassics A hcomplete S: SAME actual Hide S creator on actual complete ambient, genuine nonsimple primitive gamma; for any genuine IntrinsicPiece Q with actual IntrinsicRegionData and IntrinsicBoundaryData whose open image contains gamma trace, the actual open image of S.piece gamma is contained in Q open image. No instance for arbitrary S, no paper recording, pants, area/length/Euler or probability conclusion. data-only coherent Pi/Sigma factory: WP.External.ShortActualCutRealizationGeometry.SingleCurveCutCompanionData merely packages existing SAME actual creator companions. All cut instances share the selected genuine C; completion sources are its own cut pieces or the SAME canonical Hide S.piece. No arbitrary partial records are instantiated and no paper conclusion is a field. FullSingleCurveFillingClassics A hcomplete S adds only the SAME stable nonsimple gamma intrinsic primitive beta with exact projection, interior trace, and literal FullFilling of its own piece. FullFilling quantifies every actual complement component in the original B.Point: disk, actual boundary cylinder, or actual cusp cylinder. CuspEndBoundedBy is closed-embedded in original B.Point (not merely in the complement), preventing an artificial end approaching the removed curve. This full clause is distinct from weak InteriorFilling. No instance for arbitrary S and no paper estimate/classification/record field.

**Reference**: Hide arXiv:2107.14555v4 (2022), printed21 Definition4.9 disk/peripheral-cylinder complement, printed22 Definition4.10 and Lemma4.11(1–3), printed23 Definition4.12. actual construction keeps duplicate intrinsic boundary sides. Boundary<=2ell/area<=4ell and the exact interior simple-loop filling consequence below are classical; no G3 recording or classification is supplied. Generic bordered boundary-budget extension: Hide2107.14555v4 Def4.10/Lem4.11(2) printed21–22 (complete ambient), NWX2009.07538v3 Prop59 pp57–58 and §3 pp11–13 (closed ambient), with Martelli closed-convex geodesic-boundary lift and axial length minimization. Explicit derived extension, not HideDef4.9 as proof. Same-creator minimal supporting open-image semantics: Hide Def4.10 printed22, compared with BIPP §3.2 printed13–14 regular-neighborhood/fill/straighten and convex-hull support, Remark3.11 printed15 minimum supporting surface. this is a derived classical construction comparison, not a theorem about arbitrary containing pieces. full complement clause is exactly Hide printed21 Def4.9 and printed22 Lem4.11(1) for the SAME genuine Def4.10 creator. The coordinate presentation uses open disk homeomorphic to C, actual boundary cylinder S1 x [0,infinity) with zero circle the actual boundary trace, and open cusp cylinder S1 x R containing an actual ambient-closed embedded cusp-end region. These are ordinary coordinate forms of the cited disks/peripheral cylinders, not a new filling/count theorem.

[Read the source](https://arxiv.org/pdf/2107.14555).

**Used for**: Nonsimple G3 local topology/recording and eventual two-cusp pants identification still require local proofs; the refinement prevents redoing the already-published full individual filling theorem. No tuple or graph recording, selected-piece Euler budget, finitefiber, expectation, pants classification or Ks support bound occurs in the interface. The original literal not-filling-two-cusp-pants count is locally bounded by the already proved stronger nonpants chosen-support count, using this exact old full-filling clause and no new geometric estimate.

</details>

<a id="input-mc-cut-components"></a>

<details>
<summary>49. Geometric realization of cut components (MC-CUT-COMPONENTS)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-mc-cut-components).

**Lean declarations**:

- [WP.External.ShortFillingGeometry.CutComponentRealization](../WPFormalization/External/ShortFillingGeometry.lean#L116)
- [WP.External.ShortCutPantsGeometry.TwoCuspCutRealization](../WPFormalization/External/ShortCutPantsGeometry.lean#L17)
- [WP.External.ShortIntrinsicCompletionGeometry.CutCompletionRealization](../WPFormalization/External/ShortIntrinsicCompletionGeometry.lean#L27)
- [WP.External.ShortCutPantsTypeRecognitionGeometry.CutPantsTypeRecognition](../WPFormalization/External/ShortCutPantsTypeRecognitionGeometry.lean#L17)
- [WP.External.ShortActualCutRealizationGeometry.ActualCutRealizationData](../WPFormalization/External/ShortActualCutRealizationGeometry.lean#L19)

**Precise statement and conditions**: Same actual A/H/T, existing actual ordered orbit o and actual tuple kappa with proved T.orbitMem o X kappa. Intrinsic pieces correspond exactly to connected components of the complement of the actual cut traces. Their genera equal T.cut.genus, cusp fibers are original named cusps, boundary fibers are the two actual cut half-sides, and projected boundary primitive equals the corresponding actual kappa edge. No claim that an arbitrary filled piece is a cut component. TwoCuspCutRealization hcomplete R concerns this SAME existing actual cut R, actual complete ambient, D.genus=0 and actual original-cusp fiber.card=2 and actual half-side fiber.card=1. It gives actual model.Point homeomorphic to closed unit disk minus±1/2 with actual intrinsicBoundary iff norm1. It is actual creator realization data, not an existence theorem for arbitrary partial R or arbitrary numeric B labels. Scoped companion of the SAME genuine intrinsic Q and actual cut creator R with region/boundary data and explicit complete ambient. Only AFTER a local literal equality of their open images does completion give actual point isometry, ambient commutation and intrinsic boundary iff. It chooses no component and returns no topology/budget/count. No instance for arbitrary partial records. CutPantsTypeRecognition hcomplete R requires the SAME actual complete ambient/cut creator; actual HasPantsTopology(R.piece c) forces its cut genus=0, original cusp-fiber card=2 and retained halfside-fiber card=1. No instance for arbitrary partial R or numerical BorderedGeometry. No waist, original-curve support, recording, Euler/length budget, finite multiplicity or probability conclusion. data-only coherent Pi/Sigma factory: WP.External.ShortActualCutRealizationGeometry.ActualCutRealizationData merely packages existing SAME actual creator companions. All cut instances share the selected genuine C; completion sources are its own cut pieces or the SAME canonical Hide S.piece. No arbitrary partial records are instantiated and no paper conclusion is a field.

**Reference**: Mirzakhani primary12July2005 author version Section2 printed11-12 defines the actual surface cut by disjoint annular neighborhoods with all original labels and two edge sides, and Section8 printed36-38 identifies actual ordered multicurve pieces. The connected-component image and labeling fields are exact semantics of that cut construction, not a short-curve recording theorem. The additional same-cut topology companion is the old finite-type classification: Martelli Ch5 Thm1.1/Def1.2 p83 and pp84–85 twice-punctured disk, with actual cusp compactifications from Ch4 Prop2.20 p81; boundary-preserving placement of punctures is an explicitly derived standard-model specialization. Same actual open-piece metric completion uniqueness: Martelli printed52–54 (explicit uniqueness paragraph p54) and complete cusps pp80–81; a derived same-interior completion isometry with commuting ambient maps and exact formal boundary iff. Reverse finite-type recognition for SAME actual cut creator: Martelli Ch5 Thm1.1/Def1.2 printed83, actual cusp compactification pp80–81, Mirzakhani2005 actual cut definition pp11–13. derived ordinary classification semantics, not a G3 curve-recording theorem.

[Read the source](https://www.math.stonybrook.edu/~mlyubich/Archive/Geometry/Teichmuller%20Space/Mirz3.pdf).

**Used for**: Local connected-filled-interior-to-cut-component theorem and later G3 actual record construction. Connected-set containment is proved with Mathlib, not supplied as a field.

</details>

<a id="input-wp-genus0-boundary"></a>

<details>
<summary>50. Comparison of genus-zero WP volumes with boundaries (WP-GENUS0-BOUNDARY)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-wp-genus0-boundary).

**Lean declarations**:

- [WP.External.wpVolume_genus_zero_boundary_upper](../WPFormalization/External/BoundaryVolumeComparison.lean#L22)

**Precise statement and conditions**: P:PsiTheory; G:WeilPeterssonGeometry P; exactly genus zero; n>=3; all physical boundary lengths L_i>=0. wpVolume G 0 n L <= exp((sum_i L_i)/2)*cuspVolume G 0 n, with V0,3=1. No constants depending on n or boundary dimension. No claim for unstable types.

**Reference**: Mirzakhani JDG94(2013), printed279 Lemma3.2(2), Eq3.7; independently checked Shen-Wu arXiv2203.15681v4 PDFp11 Lemma14(1), all stable g,n. Arbitrary normalized PsiTheory/WeilPeterssonGeometry transfer uses classical DVV uniqueness and WP polynomial normalization; this transfer remains part of the deferred proof, not a local Lean implication.

[Read the source](https://archive.ymsc.tsinghua.edu.cn/pacm_download/21/977-4.3760.pdf).

**Used for**: Missing stable genus-zero leaf upper bound in local proof of original14.7 and the uniform-all-k planar marked-tail truncation for14.1. Genus>=1 stronger estimates remain proved locally.

</details>

<a id="input-top-regular-neighborhood"></a>

<details>
<summary>51. Regular neighborhoods of finite graphs in surfaces (TOP-REGULAR-NEIGHBORHOOD)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-regular-neighborhood).

**Lean declarations**:

- [WP.External.ShortRegularNeighborhoodGeometry.NeighborhoodData](../WPFormalization/External/ShortRegularNeighborhoodGeometry.lean#L29)
- [WP.External.ShortRegularNeighborhoodGeometry.RegularNeighborhoodClassics](../WPFormalization/External/ShortRegularNeighborhoodGeometry.lean#L45)

**Precise statement and conditions**: B is the same actual orientation-preserving finite-area hyperbolic quotient with domain=univ. N is an actual finite EmbeddedNetwork, loops and multiple edges allowed, all vertices covered by endpoints, exact compact support. Returns actual compact regular-closed neighborhood containing support in its interior, actual frontier homeomorphism from rho*reverse dart-interval quotient, continuous retract and strong deformation fixed on support, and exact boundary retraction onto parametrized graph walk. Edge universe independent of primitive-class universe. No filling, Euler bound, graph budget, cut, multiplicity or paper G3 conclusion.

**Reference**: Lazarus–de Mesmay, Surfaces and embedded graphs (author5Oct2017), printed2 embedded graphs and8–9 Fig9 vertex-disks/edge-bands. The compact region/frontier/dart quotient/strong deformation and parametrized retract in a cusped ambient surface are the explicitly derived local finite-chart disk-and-band corollary around compact graph support, not a literal noncompact theorem.

[Read the source](https://pagesperso.g-scop.grenoble-inp.fr/~lazarusf/Enseignement/compuTopo3.pdf).

**Used for**: Local G3 construction of actual short-curve filling from the already proved finite embedded network; all recording/classification and expectation arguments remain local.

</details>

<a id="input-top-surface-euler"></a>

<details>
<summary>52. Finite CW decompositions and Euler characteristics of surfaces (TOP-SURFACE-EULER)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-surface-euler).

**Lean declarations**:

- [WP.External.ShortSurfaceEulerGeometry.FiniteSurfaceCWModel](../WPFormalization/External/ShortSurfaceEulerGeometry.lean#L17)
- [WP.External.ShortSurfaceEulerGeometry.SurfaceCellularEulerClassics](../WPFormalization/External/ShortSurfaceEulerGeometry.lean#L39)

**Precise statement and conditions**: Any actual finite 2D Mathlib CW complex with an actual HomotopyEquiv to the SAME B.surface.Point. Counts are Nat.card of the actual Mathlib cell types. Integer card0-card1+card2= -B.negativeEuler, which is already fixed by actual area/(2pi). No existence of a network-specific cell model and no prescribed edge count.

**Reference**: Hatcher Algebraic Topology author text Theorem2.44 printed146–147: finite CW Euler equals alternating homology ranks and is homotopy invariant; combine Martelli Ch4 cusp-core/truncation p71 and geodesic double p81, Ch5 Gauss–Bonnet p84. This is the explicitly derived combination, not a claim Hatcher alone identifies hyperbolic metadata.

[Read the source](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf).

**Used for**: Locally proved negativeEuler_le_one_cells, followed by actual network CW and filling surgery construction for G3. No G3 complexity bound is an input.

</details>

<a id="input-hyp-pants-family"></a>

<details>
<summary>53. Marked families of pairs of pants with two cusps (HYP-PANTS-FAMILY)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-pants-family).

**Lean declarations**:

- [WP.External.PantsCluster.Family](../WPFormalization/External/PantsFamily.lean#L28)

**Precise statement and conditions**: Every positive waist s has an actual convex hyperbolic quotient model, actual homeomorphism to the closed complex unit disk minus ±1/2 with intrinsic boundary exactly the unit circle, genus0/cusps2/boundaries1, actual boundary realization of length s, double, and primitive/deck markings compatible with actual conjugacy/inversion and waist. Numeric genus/cusp labels alone are explicitly insufficient. No cluster measure, support, finite-catalog bound, continuity or stochastic conclusion is a field.

**Reference**: Martelli, Hyperbolic geometry, surfaces, and 3-manifolds, author18Dec2013 Ch5 Proposition1.6 printed84–87, construction/classification of hyperbolic pants including cusp cuffs of length0; standard Fenchel–Nielsen marking and boundary double.

[Read the source](https://web.dm.unipi.it/martelli/didattica/matematica/2014/Hyperbolic%20geometry.pdf).

**Used for**: Locally defined actual full primitive cluster K_s, Radon/integer point measure, finite catalog and complete geometric spectrum; paper G/14.6 conclusions remain local.

</details>

<a id="input-hyp-pants-deformation"></a>

<details>
<summary>54. Metric comparison under deformations of pairs of pants (HYP-PANTS-DEFORMATION)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-pants-deformation).

**Lean declarations**:

- [WP.External.PantsCluster.DeformationClassics](../WPFormalization/External/PantsFamily.lean#L85)

**Precise statement and conditions**: For the same marked Family F, every B>0 admits C>0 such that positive s,t≤B with |log(s/t)|≤2 and every actual marked primitive class gamma satisfy length_s(gamma)≤(1+C|log(s/t)|)length_t(gamma). Includes nonsimple classes; class marking is the same genuine deck marking. No K_s count, continuity, support or process assumption.

**Reference**: Bishop, Quasiconformal mappings of Y-pieces, RevMatIberoam18(2002), Theorem1.1 printed628 and Lemma6.2 printed651, explicitly permits unchanged two cuffs to be punctures; Bers ActaMath141(1978) Lemma1 printed81–82 (Wolpert annular-cover length comparison for every closed geodesic). Apply reflected quasiconformal double.

[Read the source](https://ems.press/content/serial-article-files/38027).

**Used for**: Local marked-length continuity, common compact-waist finite catalogs and genuine K_s vague continuity.

</details>

<a id="input-hyp-pants-uniqueness"></a>

<details>
<summary>55. Metric uniqueness of pairs of pants with two cusps (HYP-PANTS-UNIQUENESS)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-pants-uniqueness).

**Lean declarations**:

- [WP.External.PantsCluster.UniquenessClassics](../WPFormalization/External/PantsFamilyUniqueness.lean#L30)

**Precise statement and conditions**: Actual B has explicit HasPantsTopology (homeomorphism to twice-punctured closed disk identifying intrinsic boundary), actual BoundaryRealization and one boundary. Returns an actual point IsometryEquiv to F.model at its positive actual waist length, plus induced full primitive equivalence preserving length and actual trace, mapping waist to waist. No assertion arbitrary intrinsic filling has pants topology.

**Reference**: Martelli Ch5 Proposition1.6 printed84–87, uniqueness of actual geodesic-boundary pants for cuff lengths including zero cusp cuffs; primitive length/trace transport is induced by the actual isometry.

[Read the source](https://web.dm.unipi.it/martelli/didattica/matematica/2014/Hyperbolic%20geometry.pdf).

**Used for**: Local equality of the complete intrinsic primitive counting measure and K_s; canonical filling, support s≤2ell and cluster decomposition remain separate new obligations.

</details>

<a id="input-prob-vague-topology"></a>

<details>
<summary>56. The vague topology on point measures and positive rescaling (PROB-VAGUE-TOPOLOGY)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-prob-vague-topology).

**Lean declarations**:

- [WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable](../WPFormalization/External/PointMeasureDilationTopology.lean#L19)
- [WP.External.pointMeasure_nnreal_dilation_joint_continuous](../WPFormalization/External/PointMeasureDilationTopology.lean#L26)

**Precise statement and conditions**: Existing genuine PointMeasure NNReal with topology induced by actual C_c real integrals: MetrizableSpace and SecondCountableTopology. Actual PositiveScale={a:NNReal|0<a} with subtype topology; joint continuity of locally defined actual measure.map(x↦a*x). Strict positivity is required; no claim of subspace completeness. No probability convergence, WP geometry, genus, count weights or random-scale conclusion.

**Reference**: Kallenberg, Foundations of Modern Probability 2ed(2002), TheoremA2.3(i) printed564, Radon vague space Polish; hereditary metrizable/second-countable restriction to genuine integer-valued measure subspace. Joint dilation continuity is an explicitly derived compact-test/common-support/cutoff-mass corollary, not a literal separately named theorem.

[Read the source](https://doi.org/10.1007/978-1-4757-4015-8).

**Used for**: Local varying-space metric Slutsky and continuous-mapping proof for physical scale replacement in original14.5.

</details>

<a id="input-top-loop-straightening"></a>

<details>
<summary>57. Geodesic straightening of closed-loop homotopy classes (TOP-LOOP-STRAIGHTENING)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-loop-straightening).

**Lean declarations**:

- [WP.External.ShortLoopStraighteningGeometry.LoopStraighteningClassics](../WPFormalization/External/ShortLoopStraighteningGeometry.lean#L73)

**Precise statement and conditions**: Same actual complete-domain finite-area orientation-preserving hyperbolic quotient B. ClosedLoop is actual continuous [0,1] map with equal endpoints; Simple injective on [0,1); actual Mathlib free homotopy with closed endpoints; actual total variation length. PositiveHomotopyLength literally bounds lengths of every freely homotopic loop away from0. Exact5fields: simple positive class primitive representative, actual primitive free homotopy iff class equality, minimum actual length, simple geodesic representative, and same-or-disjoint geodesics from actual disjoint simple representatives. No filling or G3 classification.

**Reference**: Farb–Margalit, A primer on mapping class groups, author Version5.0 January2011, printed22 puncture classes, Proposition1.3 pp25–26, Proposition1.4 pp27–28, Proposition1.6 pp28–29, Corollary1.9 p34 and multicurves p35. Length-minimization is the explicitly derived lift/axis endpoint-distance corollary, including infinite-variation loops, not a literal separately numbered inequality.

[Read the source](https://pagine.dm.unipi.it/~a019210/Farb%20Magalit_Primer%20on%20Teichmuller%20theory.pdf).

**Used for**: Local actual RN boundary straightening; positive homotopy length, boundary length, duplicate class handling and G3 recording remain local obligations.

</details>

<a id="input-top-simple-annulus"></a>

<details>
<summary>58. Annuli between disjoint homotopic simple closed curves (TOP-SIMPLE-ANNULUS)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-simple-annulus).

**Lean declarations**:

- [WP.External.ShortLoopStraighteningGeometry.SimpleAnnulusClassics](../WPFormalization/External/ShortLoopStraighteningGeometry.lean#L91)

**Precise statement and conditions**: Same complete actual B; actual simple closedloops f,g, f positive homotopy length, unoriented free homotopy and disjoint actual traces. Returns actual compact annulus embedding LoopCircle×[0,1] into SAME surface, exact two boundary maps up to homeomorphism reparametrization. No claim original network avoids annulus, no component/cusp allocation, no graph collapse or filled record.

**Reference**: Farb–Margalit Version5.0 January2011 Proposition1.10 proof printed35–36, actual lift-strip quotient annulus; surface convention printed18 includes punctures and boundary. This uses the punctured-surface statement, not a closed-only annulus theorem.

[Read the source](https://pagine.dm.unipi.it/~a019210/Farb%20Magalit_Primer%20on%20Teichmuller%20theory.pdf).

**Used for**: Local proof of empty-annulus collapse and retention of cusp-containing cylinders in G3; these are not interface fields.

</details>

<a id="input-top-simple-complement"></a>

<details>
<summary>59. Simple closed curves, disks, and cusp ends (TOP-SIMPLE-COMPLEMENT)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-simple-complement).

**Lean declarations**:

- [WP.External.ShortComplementaryRegionGeometry.SimpleComplementClassics](../WPFormalization/External/ShortComplementaryRegionGeometry.lean#L37)

**Precise statement and conditions**: Same actual complete-domain finite-area orientation-preserving hyperbolic B and arbitrary actual Simple ClosedLoop f. Returns PositiveHomotopyLength OR actual closed complex unit disk embedding with full boundary f, open interior and actual frontier f.trace OR actual closed embedding of LoopCircle×[0,infinity) with exact boundary, open interior and frontier f.trace. No chosen cusp label/function, tuple/network avoidance, simultaneous fillings or cut data.

**Reference**: Farb–Margalit authorVersion5 January2011 printed22 deck/cusp classification and Prop1.3 pp25–26 axis-length comparison; Marden–Richards–Rodin, On the regions bounded by homotopic curves, PacificJMath16(2)(1966) printed337–339, assertions(i)/(ii) null simple disk and disjoint homotopic nontrivial annulus, explicitly compact or noncompact orientable surfaces; Martelli author18Dec2013 Ch4 actual finite-area cusp ends. Trichotomy is the explicitly derived combination, not a literal single theorem.

[Read the source](https://msp.org/pjm/1966/16-2/pjm-v16-n2-p13-s.pdf).

**Used for**: Local construction of admissible actual complementary disk/cusp surgeries for G3. Selecting the side avoiding the graph, simultaneous disjoint filling, retained annuli, CW budget and actual record/classification remain local new proofs.

</details>

<a id="input-prob-poisson-laplace"></a>

<details>
<summary>60. The Laplace functional of Poisson random measures (PROB-POISSON-LAPLACE)</summary>

**Remaining work**: Formalize the classical proof. See [the specific obligations](INFRASTRUCTURE.md#task-prob-poisson-laplace).

**Lean declarations**:

- [WP.External.poisson_laplace_functional](../WPFormalization/External/PoissonLaplaceFunctional.lean#L21)

**Precise statement and conditions**: E lcsc Hausdorff Borel, actual locally finite Regular intensity ν, genuine existing pointmeasure probability law QL with independent Poisson counts on finite disjoint windows. Every nonnegative globally bounded Borel h with support contained in a compact K: actual exponential of -Bochner integral ξh is Borel and expectation equals exp(- integral (1-exp(-h)) dν). Local finiteness/compact support/boundedness ensure finite actual integrals. Zero intensity and multiplicities allowed. No paper family or rate premise.

**Reference**: Kallenberg Foundations of Modern Probability2ed(2002), Chapter12 Lemma12.2(i) printed227 and random-integral measurability printed225; independently Last–Penrose Lectures on the Poisson Process author21Aug2017 Theorem3.9 printed23–24. Exact bounded nonnegative compactly supported Borel specialization, no geometric or convergence result.

[Read the source](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf).

**Used for**: Local independent-product Laplace identities and actual pants test-pairing wrappers; canonical proper waist support, cluster local finiteness and original WP spectrum approximation/convergence remain paper-new obligations.

</details>

<a id="input-top-cyclic-interval"></a>

<details>
<summary>61. Topology of finite interval gluings (TOP-CYCLIC-INTERVAL)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-cyclic-interval).

**Lean declarations**:

- [WP.External.FiniteCyclicIntervalGeometry.Classics](../WPFormalization/External/FiniteCyclicIntervalGeometry.lean#L37)

**Precise statement and conditions**: Every natural m>0, including1, finite quotient of m actual unit intervals by cyclic right-to-next-left endpoints. Actual AddCircle1 homeomorphism with h([(j+s)/m])=[j,s]. No graph, surface, length or recording data.

**Reference**: Hatcher Algebraic Topology Ch0 finite adjunction-space framework; explicit inverse F([j,s])=[(j+s)/m] and compact-Hausdorff proof recorded separately. Derived elementary corollary, including m=1.

[Read the source](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf).

**Used for**: Actual boundary cycle parametrizations; subsequent metric variation, Euler, recording and filled-component classification remain local.

</details>

<a id="input-hyp-bordered-loop"></a>

<details>
<summary>62. Curve straightening on convex bordered hyperbolic surfaces (HYP-BORDERED-LOOP)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-bordered-loop).

**Lean declarations**:

- [WP.External.ShortBorderedLoopGeometry.BorderedLoopStraighteningClassics](../WPFormalization/External/ShortBorderedLoopGeometry.lean#L17)

**Precise statement and conditions**: Same actual BorderedGeometry B with actual BoundaryRealization R; no false domain=univ assumption. Exact5fields: simple positive actual homotopy class primitive representative, primitive UFH iff equality, actual variation length minimum, simple representative, same-or-disjoint geodesics from disjoint simple representatives. Derived axis proof in invariant convex cover.

**Reference**: Martelli Ch3 Thm1.13/Cor1.14 pp52–53, Ch4 Prop1.14/Cor1.16 pp72–73; Farb–Margalit pp25–34. Explicit derived convex-lift axis extension.

[Read the source](https://web.dm.unipi.it/martelli/didattica/matematica/2014/Hyperbolic%20geometry.pdf).

**Used for**: Intrinsic piece curve transport and actual canonical pants topology applications. No simple-pants classification, whole filling or waist support bound is assumed.

</details>

<a id="input-hyp-primitive-boundary"></a>

<details>
<summary>63. Intrinsic primitive traces and boundary uniqueness (HYP-PRIMITIVE-BOUNDARY)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-primitive-boundary).

**Lean declarations**:

- [WP.External.ShortBorderedLoopGeometry.PrimitiveBoundaryClassics](../WPFormalization/External/ShortBorderedLoopGeometry.lean#L45)

**Precise statement and conditions**: Same actual B and BoundaryRealization R. Only injectivity of actual primitive unoriented trace and every actual primitive trace lies entirely in actual intrinsicInterior OR equals one actual R.curve j. Tangent uniqueness and actual convex geodesic boundary are essential; numeric boundary metadata alone insufficient.

**Reference**: Martelli Ch4 Ex1.11 p72 only trace/orientation/multiplicity framework; generic geodesic initial-tangent uniqueness supplies actual derived facts.

[Read the source](https://web.dm.unipi.it/martelli/didattica/matematica/2014/Hyperbolic%20geometry.pdf).

**Used for**: Local proof of primitive projection injectivity on actual one-boundary intrinsic cut pants and ambient cluster measure identification, with actual topology and boundary supplied separately.

</details>

<a id="input-hyp-peripheral-axial"></a>

<details>
<summary>64. Axial geodesics in cusp ends and compact annuli (HYP-PERIPHERAL-AXIAL)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-peripheral-axial).

**Lean declarations**:

- [WP.External.ShortPeripheralAxialGeometry.PeripheralAxialClassics](../WPFormalization/External/ShortPeripheralAxialGeometry.lean#L21)
- [WP.External.ShortBorderedPeripheralGeometry.BorderedPeripheralClassics](../WPFormalization/External/ShortBorderedPeripheralGeometry.lean#L16)

**Precise statement and conditions**: Same complete actual finite-area hyperbolic B, domain=univ. Every actual proper cusp end contains no entire actual primitive geodesic trace; every actual primitive trace contained in an actual compact annulus has UFH class of actual simple positive-homotopy-length boundary f. Actual region embeddings/frontiers retained. No network avoidance, filling, cusp allocation or budget. The bordered version retains actual R and the same two low-level cusp/annulus axial fields, without asserting domain=univ. No pants/filling/support or instance for an arbitrary realization is supplied.

**Reference**: Martelli Ch4 Cor2.19/Prop2.20 pp80–81; Farb–Margalit p22 and Props1.3–1.4; Hatcher Thm1.7 p29 and Prop1.5 p28. Explicit derived cusp/annulus cyclic-parabolic/axial combination. The same two facts on actual convex geodesic-boundary B with actual BoundaryRealization R are the derived convex-cover/cusp-double extension using Martelli Ch3 Thm1.13/Cor1.14 pp52–53 and Ch4 Prop2.20 pp80–81.

[Read the source](https://web.dm.unipi.it/martelli/didattica/matematica/2014/Hyperbolic%20geometry.pdf).

**Used for**: Local network frontier disk/cusp/annulus operations and cut avoidance. Actual disk contraction is already locally proved; no disk field added.

</details>

<a id="input-top-planar-jordan"></a>

<details>
<summary>65. Planar Jordan–Schoenflies extension (TOP-PLANAR-JORDAN)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-planar-jordan).

**Lean declarations**:

- [WP.External.PlanarJordanGeometry.PlanarJordanClassics](../WPFormalization/External/PlanarJordanGeometry.lean#L19)

**Precise statement and conditions**: Every actual continuous injective map from complex unit circle into complex plane extends to a homeomorphism of the entire plane. Compact source gives image homeomorphism, exact Theorem3.1 specialization. No hyperbolic, pants, puncture, geodesic, whole filling or count assertion.

**Reference**: Thomassen The Jordan–Schoenflies theorem and classification of surfaces (1992), Thm3.1 printed123, proof123–125; primary source.

[Read the source](https://people.math.wisc.edu/~dymarz/751/thomass.pdf).

**Used for**: Local canonical-pants planar disk and puncture partition proofs; the actual Jordan disk/norm bound are locally constructed and proved, not fields.

</details>

<a id="input-top-planar-regions"></a>

<details>
<summary>66. Coordinates on planar annuli and punctured disks (TOP-PLANAR-REGIONS)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-planar-regions).

**Lean declarations**:

- [WP.External.PlanarRegionGeometry.PlanarRegionClassics](../WPFormalization/External/PlanarRegionGeometry.lean#L24)

**Precise statement and conditions**: Only arbitrary actual DiskBoundedBy f in complex plane and p in literal interior: LoopCircle×Ici0 homeomorphism to actual closed disk image minus p, boundary maps f.circleMap exactly and positive second coordinate iff actual interior. Also arbitrary actual D/E with rangeD subset interior rangeE admit actual compact AnnulusBetween f g with exact range rangeE minus interior(rangeD). No hyperbolic, pants, curve classification, waist, filling, length or probability hypothesis/result.

**Reference**: Viro–Ivanov–Kharlamov–Netsvetaev Elementary Topology PartIII §54.Cx printed363: arbitrary two disjoint simple closed curves onS2 bound an annulus, explicitly no triangulability assumption. Precise nested planar range/boundary parametrizations are derived specializations. Punctured actual Jordan disk coordinates are the Jordan–Schoenflies + disk automorphism moving the puncture + polar-coordinate corollary, with exact boundary and interior formula, not verbatim theorem API.

[Read the source](https://www.pdmi.ras.ru/~olegviro/topoman/e-part3.pdf).

**Used for**: Local canonical pants zero/one/two-puncture classification, actual end and annulus transport. Those paper-related applications are locally proved, not fields.

</details>

<a id="input-prob-vague-pairing"></a>

<details>
<summary>67. Measurable compactly supported integrals and the vague topology (PROB-VAGUE-PAIRING)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-prob-vague-pairing).

**Lean declarations**:

- [WP.External.CompactBorelVaguePairing](../WPFormalization/External/PointMeasureMappingClassics.lean#L13)

**Precise statement and conditions**: Genuine PointMeasure NNReal with actual vague topology. Arbitrary signed Borel h, globally norm bounded and with support in a compact set; integral is Borel. For continuity at actual xi, h must be xi-a.e. continuous. No geometry, cluster properness or paper process premise.

**Reference**: Kallenberg Foundations of Modern Probability (2002), A2.3(iii),(iv), printed pp564–565. Bounded compact Borel integral measurability and continuity at a measure assigning zero mass to discontinuities are derived portmanteau/monotone-class corollaries, not a literal theorem API.

[Read the source](https://doi.org/10.1007/978-1-4757-4015-8).

**Used for**: Local finite-waist canonical cluster continuity through actual signed compact test pairings. Actual cluster maps and endpoint nullity are separately proved locally.

</details>

<a id="input-prob-ae-cmt"></a>

<details>
<summary>68. Convergence in distribution under almost-everywhere continuous maps (PROB-AE-CMT)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-prob-ae-cmt).

**Lean declarations**:

- [WP.External.AlmostSureContinuousMapping](../WPFormalization/External/PointMeasureMappingClassics.lean#L24)

**Precise statement and conditions**: Arbitrary metrizable second-countable Borel source and target spaces, varying measurable probability spaces eventually in the sequence, eventual AE measurability of Xj, actual probability limiting space and AE measurable Z; fixed Borel f continuous at Z almost surely. Genuine LawConverges of Xj to Z. No WP, pants, support, or geometric assumption in the interface.

**Reference**: Kallenberg Foundations of Modern Probability (2002), Theorem4.27, printed pp76–77, fixed-map a.s.-continuity case. Changing source probability spaces is the pushforward-law/cofinal-tail formulation.

[Read the source](https://link.springer.com/chapter/10.1007/978-1-4757-4015-8_4).

**Used for**: Local finite-waist cluster mapping convergence once actual map Borel and limiting endpoint/discontinuity-nullity are proved; no actual WP spectrum approximation is supplied.

</details>

<a id="input-prob-ppp-first"></a>

<details>
<summary>69. The first arrival of a marked Poisson process (PROB-PPP-FIRST)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-prob-ppp-first).

**Lean declarations**:

- [WP.External.MarkedPoissonFirstPointData](../WPFormalization/External/MarkedFirstPoint.lean#L30)

**Precise statement and conditions**: Arbitrary locally finite regular diffuse Borel ν on NNReal with νuniv=∞, arbitrary finite positive η on Nat, genuine PPP law for ν.prodη. Returns actual AE first-state map into ENNReal×Nat, a.s. whole-mark prefix finiteness and unique finite first atom, exact first-arrival law and its probability normalization. No WP objects, q, systole, density limit or paper estimates.

**Reference**: Last–Penrose Lectures on the Poisson Process, author manuscript21Aug2017, §7.2 Theorem7.4(i) n=1, Corollary7.5, measurable enumeration(7.7)/Exercise7.4, printed61–63. Diffuse time and finite positive mark mass give the ordinary projection and a.s. unique finite first atom.

[Read the source](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf).

**Used for**: Actual systole and cusp-type joint law from already proved actual markedPPP, selector validity and noescape. Quadratic 2t wk exp(-W t²), mark wk/W and actual geometric selector conditions are proved locally.

</details>

<a id="input-prob-first-cmt"></a>

<details>
<summary>70. Convergence in distribution of the selected first point (PROB-FIRST-CMT)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-prob-first-cmt).

**Lean declarations**:

- [WP.External.MarkedFirstPointConvergence](../WPFormalization/External/MarkedFirstPoint.lean#L48)

**Precise statement and conditions**: Arbitrary varying probability spaces eventually, actual marked PointMeasure(NNReal×Nat) variables and AE selected ENNReal×Nat states; actual vague convergence; a.s. whole-mark time-prefix finiteness, uniform bounded-time high-mark noescape; outer probability of invalid actual minimum selection tends0; limiting process has AE measurable, unique finite first atom and whole-mark prefix finiteness. Selector may depend on Ω and use arbitrary ties. No PPP intensity or paper geometric conclusion is a field.

**Reference**: Derived finite-window classical corollary of Kallenberg Foundations of Modern Probability2002 Theorems4.27–4.28 printed76–78 and A2.3 printed564–565. Not asserted to be a verbatim source theorem: finite-window atom matching + time/mark truncation + negligible invalid selection.

[Read the source](https://link.springer.com/chapter/10.1007/978-1-4757-4015-8_4).

**Used for**: Apply to actual shortest primitive curve/tie-selected cusp type after all geometric validity/noescape/prefix and markedPPP conditions are locally proved. This supplies only the generic probability inference.

</details>

<a id="input-hyp-finite-support"></a>

<details>
<summary>71. Convex supporting subsurfaces for finite geodesic sets (HYP-FINITE-SUPPORT)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-finite-support).

**Lean declarations**:

- [WP.External.ShortSupportingPieceGeometry.SupportingPieceData](../WPFormalization/External/ShortSupportingPieceGeometry.lean#L37)
- [WP.External.ShortSupportingPieceGeometry.SupportingPieceClassics](../WPFormalization/External/ShortSupportingPieceGeometry.lean#L49)
- [WP.External.ShortSupportingConstructionGeometry.SupportingBoundaryRealization](../WPFormalization/External/ShortSupportingConstructionGeometry.lean#L18)
- [WP.External.ShortSupportingConstructionGeometry.SupportingCarrierRealization](../WPFormalization/External/ShortSupportingConstructionGeometry.lean#L29)
- [WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions](../WPFormalization/External/ShortTupleRecordingGeometry.lean#L19)
- [WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.neighborhood](../WPFormalization/External/ShortTupleRecordingGeometry.lean#L19)
- [WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.surface](../WPFormalization/External/ShortTupleRecordingGeometry.lean#L19)
- [WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.carrier](../WPFormalization/External/ShortTupleRecordingGeometry.lean#L19)
- [WP.External.ShortTupleRecordingGeometry.TupleRecordingCompanions.boundary](../WPFormalization/External/ShortTupleRecordingGeometry.lean#L19)

**Precise statement and conditions**: Same genuine complete finite-area BorderedGeometry B with explicit domain=univ, nonempty finite set of actual primitive axial geodesics, preconnected actual carrier and exclusion of a single simple primitive carrier. Returns actual IntrinsicPiece with ordinary region/boundary data, contains every actual trace, actual connected lift component, exact projection of interior of its closed geodesic hull, minimal actual interior inclusion among genuine such pieces. No length/Euler/recording/count/rate or pants conclusion. Scoped DATA only for SAME genuine support Q and actual carrier/RN N,D: actual formal boundary sides inject into actual RN surviving cycles with literal unorientedfreehomotopy; actual continuous graphcarrier interiorlift commuting with ambient inclusion induces surjective actual FundamentalGroup.map. No existence for arbitrary unrelated partial Q/N/D, no card/length/Euler budget/recording/expectation supplied. TupleRecordingCompanions is only coherent dependent data packaging on actual H tuple gamma with injectivity/simple/length proofs and L>0: actualAmbientTuple=A.primitiveEquiv composed with gamma; neighborhood only for its exact tupleEmbeddedNetwork; surface/carrier/boundary only for SAME SP activeClusterSupport and actual activeSupportNetwork; boundary uses that exact neighborhood. No all-arbitrary-partial N/Q instances and no selection/Euler/length/card/record/count/rate conclusion. neighborhood reuses TOP-REGULAR-NEIGHBORHOOD, surface reuses TOP-SURFACE-PI1, and carrier/boundary reuses this group.

**Reference**: Burger–Iozzi–Parreau–Pozzetti A structure theorem for geodesic currents and length spectrum compactifications, author manuscript5Dec2017, §3.2 printed13–15. Finite connected carrier regular neighborhood/fill disks and once-cusps/straighten construction p14, convex limit-set hull description p14, minimality Def3.10/Remark3.11 p15. Literal actual lift hull/minimality API is a derived finite-carrier specialization, not verbatim. Same-creator construction companions: BIPP printed14 actual regular-neighborhood/fill/straighten surviving formal boundary sides and literal graph-subgroup image equals pi1 of supporting surface; convex inclusion is pi1-injective. These are explicit derived creator semantics, not numeric bounds.

[Read the source](https://people.math.ethz.ch/~iozzi/submitted_PML.pdf).

**Used for**: Canonical ordinary supporting subsurface semantics for local G3 region identification and recording. Actual finite topology, boundary budget, selected components and critical O(g^-1/2) counting remain local obligations.

</details>

<a id="input-top-graph-pi1"></a>

<details>
<summary>72. Fundamental groups of finite connected graphs (TOP-GRAPH-PI1)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-graph-pi1).

**Lean declarations**:

- [WP.External.ShortFundamentalGroupGeometry.FiniteGraphFundamentalGroupClassics](../WPFormalization/External/ShortFundamentalGroupGeometry.lean#L18)

**Precise statement and conditions**: Arbitrary actual T2 topological space X with finite one-dimensional Mathlib CWComplex on univ, actual cells in dimensions≥2 empty, PreconnectedSpace X and actual basepoint x. Actual FundamentalGroup X x has finite generating set with card≤Nat.card actual1cells. No embeddednetwork, carrier, surface, geometriccut, cutoff or expectation in this type.

**Reference**: Hatcher Algebraic Topology Props1A.1/1A.2 printed84–85, full maximal-tree/freebasis proof. Stated finite actual1cell generator bound is the immediate weaker cardinality corollary; basepoint change uses pathconnectedness of connectedCW graphs.

[Read the source](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf).

**Used for**: LOCAL composition of actualcarrier pi1-surjection with actual graph generators; local finite-image/card proofs give supporting-piece Euler≤actualN.Edge, not an external field.

</details>

<a id="input-top-surface-pi1"></a>

<details>
<summary>73. Fundamental groups of orientable hyperbolic surfaces of finite area (TOP-SURFACE-PI1)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-top-surface-pi1).

**Lean declarations**:

- [WP.External.ShortFundamentalGroupGeometry.SurfaceFundamentalGroupClassics](../WPFormalization/External/ShortFundamentalGroupGeometry.lean#L32)

**Precise statement and conditions**: Same genuine connected finitearea oriented hyperbolic geodesic-boundary B, actual quotient topological space and actual GaussBonnet negativeEuler. Every finite actualpi1 generating set at each actual basepoint has cardinality≥B.negativeEuler. Closed rank2g≥2g−2; nonclosed rank2g+c+b−1=negativeEuler+1. No instance for inconsistent arbitrary partial metadata; no graph/network/recording or paper budget in type.

**Reference**: Hatcher Cor1.27 proof printed51 gives closed orientable genus-g abelianization Z^(2g); Ex1B.2 printed87 gives nonclosed surfaces retract to graphs; Prop1A.2 pp84–85, standard polygon presentation pp50–51. Martelli finite-type classification printed83 and actual cusp compactification pp80–81; combine with actualGaussBonnet. Derived generator inequality, not verbatim API.

[Read the source](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf).

**Used for**: LOCAL lower bound combined with actualgraph carrier pi1 surjection and generic finitegraph basis to prove supporting Euler budget. No new uniform cut estimate is assumed.

</details>

<a id="input-prob-ppp-restriction"></a>

<details>
<summary>74. Restriction and independence of Poisson processes (PROB-PPP-RESTRICTION)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-prob-ppp-restriction).

**Lean declarations**:

- [WP.External.TwoColorPoissonRestrictionIndependence](../WPFormalization/External/PoissonRestrictionIndependence.lean#L12)

**Precise statement and conditions**: Arbitrary locally finite Borel measures nu,mu on NNReal; genuine PPP probability law Q on PointMeasure(NNReal sum NNReal) with sum-space intensity twoColorMeasure nu mu. The actual twoColorLeftProjection and twoColorRightProjection are independent random elements under Q. No geometry, kernel, convergence or paper estimate field; no actual instance supplied.

**Reference**: Last–Penrose Lectures on the Poisson Process, author manuscript21Aug2017, Theorem5.2 restriction theorem and complete proof, printed39; Theorem5.1 mapping, printed38–39. 

[Read the source](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf).

**Used for**: Identify the two genuine restrictions of the G4 limiting sum-space PPP as independent parent processes for the canonical cluster limit. Marginal PPP laws, product-law identification, canonical kernels and double-exponential Laplace formula are locally proved.

</details>

<a id="input-prob-pm-laplace-cmt"></a>

<details>
<summary>75. Convergence in distribution of point measures from Laplace functionals (PROB-PM-LAPLACE-CMT)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-prob-pm-laplace-cmt).

**Lean declarations**:

- [WP.External.PointMeasureLaplaceConvergence](../WPFormalization/External/PointMeasureLaplaceConvergence.lean#L14)

**Precise statement and conditions**: Actual PointMeasure NNReal with the genuine vague topology, arbitrary changing measurable source spaces, eventually probability source measures and eventually AEM observed point-measure maps, arbitrary probability target with AEM point-measure map. Convergence of actual expectations of exp(-integral f) for every nonnegative compactly supported continuous real f implies genuine LawConverges. No simplicity, Poisson law, WP geometry, canonical kernel or comparison event is assumed; no instance supplied.

**Reference**: Kallenberg Foundations of Modern Probability (2002), Theorem16.16(i) iff(ii) and complete proof, printed316–317; Theorem5.3 Laplace-transform continuity and proof, printed86–87. Derived by applying transform continuity to every nonnegative scalar multiple t*f, then the genuine vague random-measure criterion. 

[Read the source](https://doi.org/10.1007/978-1-4757-4015-8).

**Used for**: Transfer actual bounded-window spectrum equality off a vanishing outer-probability event to full vague law with the already constructed canonical cluster target. Prefix comparison, outer-event estimates, Laplace transfer and all WP convergence obligations are proved locally.

</details>

<a id="input-ppp-integral-moments"></a>

<details>
<summary>76. Integrals and moments of Poisson point processes (PPP-INTEGRAL-MOMENTS)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-ppp-integral-moments).

**Lean declarations**:

- [WP.External.PoissonIntegralMoments](../WPFormalization/External/PoissonIntegralMoments.lean#L17)

**Precise statement and conditions**: Locally finite intensity on NNReal, a probability law satisfying disjoint-window PPP counts, measurable real f bounded globally and supported in Iic R. The Poisson integral has MemLp for every natural exponent, mean integral f dμ, variance integral f² dμ. For these hypotheses every deterministic and random integral is finite. No instance asserted.

**Reference**: Last–Penrose, Lectures on the Poisson Process, author manuscript 21 August 2017, Proposition 2.7 (printed p.13), Eq.(4.26) (printed p.35); Chapter 1 Poisson exponential moments.

[Read the source](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf).

**Used for**: Only generic scalar Poisson integrals; local ClusterWindowCounts/Moments proves the actual canonical cluster count identification, boundedness, support, finite moments and (14.22) via Mathlib product variance. Also rules out PPP laws from strict excess.

</details>

<a id="input-hyp-pants-figure-eight"></a>

<details>
<summary>77. Figure-eight curves in hyperbolic pairs of pants (HYP-PANTS-FIGURE-EIGHT)</summary>

**Remaining work**: Construct an instance for the intended objects and prove its properties. See [the specific obligations](INFRASTRUCTURE.md#task-hyp-pants-figure-eight).

**Lean declarations**:

- [WP.External.PantsCluster.FigureEightClassics](../WPFormalization/External/PantsFigureEight.lean#L15)

**Precise statement and conditions**: For each actual marked two-cusp pants with positive waist s, there exists a primitive unoriented class distinct from the waist, of length 2 arcosh(2+cosh(s/2)). The formula specializes the classical three-boundary trace identity at cusp lengths 0,0. Primitivity and boundary distinction use the reduced word a⁻¹b in the free pants group (or its one transverse double point); these are part of the deferred classical consequence, not claims separately machine-proved here.

**Reference**: Rivin, Advances in Mathematics 231 (2012), 2391–2412, Theorem 1.3; arXiv:0901.2543 preprint Theorem 2 Eq.(1), and its cusp equality in Corollary 3.

[Read the source](https://arxiv.org/abs/0901.2543).

**Used for**: Local proofs show for L>2 arcosh3 both distinct classes lie below L for a small positive interval of s. They then prove positive μ_c mass, strict integrated excess and non-Poisson. No cluster probability or multiplicity estimate is an external field.

</details>

<a id="proved-tools"></a>

## Completed background tools

[Bounded optional stopping](../WPFormalization/Probability/BoundedOptionalStopping.lean) is proved using Mathlib theorems and is not an outstanding classical premise.
Other completed library results and auxiliary tools are identified by the references in their Lean source files.

## Scope of the cited classical results

<a id="mirzakhani"></a>

<details>
<summary>Multicurve integration and short curves</summary>

`MirzakhaniIntegration` uses the classical integration formula for an orbit of ordered, disjoint, simple multicurves.
The integrand is the actual orbit sum; the volume after cutting is the product of the component volumes, and the length measure includes the product of the lengths.
The coefficient is determined by the number of one-handles and the index of the orientation-preserving stabilizer, rather than chosen freely.

The source is [Shen–Wu, arXiv:2203.15681v4](https://arxiv.org/pdf/2203.15681v4), §2.2, Theorem 6 (PDF p. 7) and the following remark.
Lemma 29 (pp. 22–23) applies this formula to labeled pants orbits; its asymptotic moment conclusion is not taken as a classical input.
The project separately proves the labeled counts, asymptotic estimates, and probability limits.

The geometric interface requires surfaces of finite type, allowing cusps. Local finiteness of the length spectrum and measurability of length functions are also required classical facts.
For finite-type surfaces with cusps, see [Erlandsson–Parlier, §2](https://research-information.bris.ac.uk/files/194628295/Ksystoles2016_11_03.pdf).
Measurability follows from continuous length functions on Teichmüller space, countably many free homotopy classes, and descent to moduli space.
This is an explanation of a consequence of the source, not a claim that it states the Lean structure verbatim.

Primitive closed geodesics shorter than `2 arsinh(1)` are simple; two distinct simple closed geodesics in this range are disjoint.
These statements refer to Buser Theorems 4.4.6 and 4.1.6, respectively; the theorem numbers must not be interchanged.
[Hide–Thomas, arXiv:2209.15568v3](https://arxiv.org/pdf/2209.15568v3), pp. 1 and 8, gives the corresponding references and their use for surfaces with cusps.

</details>

<a id="tight-transform"></a>

<details>
<summary>The classical transform for tight-boundary volumes</summary>

The original source is [Budd–Zonneveld, arXiv:2307.04708](https://arxiv.org/pdf/2307.04708), Proposition 12, printed p. 21, equations (69)–(70):

```text
Ftilde_g[nu,mu] = 2^(3g-3) G_g(0; tau_0,tau_1,...)
tau_k = t_k[nu] + delta_{k,1} - 2^(1-k) M_{k-1}[mu]
t_k[nu] = integral 2 L^(2k)/(4^k k!) dnu(L).
```

The time variables are in equation (68), and the intersection generating series is in equation (65). The geometric objects are Weil–Petersson volumes of actual restricted regions.
`ProtectedCycleGeometry` and `TightRegions` describe actual simple closed curves, free homotopy classes after capping, and measurability of the specified tight-boundary regions.
Each region is defined by the precise condition on the unique shortest representative, rather than specified as an arbitrary set.

`BuddZonneveldTransform.weighted_taylor` uses only the coefficient-level transform: the finite measure is supported in some `[0,B]`,
and the analytic root germ satisfies `R(0)=0` and `Z_mu(R(t),t)=0`, where

```text
Z_mu(r,t) = X(P r)/P - t * integral I0(L sqrt(2r)) dmu(L)
M_j(t) = partial_r^(j+1) Z_mu(R(t),t),   P = 2*pi^2.
```

The `I0` kernel is represented by the entire series `sum_j (L^2*r/2)^j/(j!)^2`, without introducing a square-root branch.
The interface does not assume a summed identity at nonzero real parameters or global convergence; these properties and the paper's specialization are proved separately.
Check the full range of stable parameters, including the unmarked case, against the formal theorem types.

</details>

<a id="point-process"></a>

<details>
<summary>Classical probability inputs for point processes</summary>

Point measures are locally finite, integer-valued Radon measures, allowing multiplicities.
The vague topology used here is induced by integration against actual compactly supported continuous functions. Convergence in distribution uses bounded continuous test functions on this topology.
Limits of count vectors are not the definition of this topology.

- [Kallenberg, *Foundations of Modern Probability*, 2nd ed.](https://doi.org/10.1007/978-1-4757-4015-8_16): A2.3(iv), p. 564; Lemma 16.15 and Theorem 16.16(iii)⇒(i), pp. 316–317. These provide the measurable structure for counts and integrals and the convergence criterion for point measures.
- [Last–Penrose, *Lectures on the Poisson Process*](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf): Theorem 3.6 and Corollary 3.7, p. 21. Locally finite Radon intensities apply on locally compact, second-countable Hausdorff spaces; atoms and multiplicities are generally allowed.
- [Hide–Thomas, arXiv:2209.15568v3](https://arxiv.org/html/2209.15568v3): Proposition 3.1, p. 7. This is a multivariate falling-factorial-moment criterion with strictly positive rates, allowing varying probability spaces.

Zero-rate coordinates are handled by first moments, Markov's inequality, and a finite union bound, before restoring the coordinates that are deterministically zero. This is a consequence of the positive-rate criterion.
The semiring-window criterion also requires countable generation, local approximation, and control of mass on compact sets, followed by approximation of compactly supported continuous functions by simple functions.
The almost-everywhere measurable version requires measurable representatives; an "eventually" hypothesis can be handled by discarding a finite prefix.
These deductions do not replace arguments with invalid uncountable unions of null sets or the default values of nonintegrable integrals.
See the [list above](#external-inputs) for the exact conditions and uses of the relevant premise groups; look for identifiers beginning with `PROB-` or `PPP-`.

</details>

<a id="hyperbolic-packing"></a>

<details>
<summary>Local area, collars, and doubling of hyperbolic surfaces</summary>

Main sources:
[Parlier, *Interrogating surface length spectra and quantifying isospectrality*](https://homeweb.unifr.ch/parlierh/pub/Papers/Isospectral2016-11-07.pdf), pp. 4–6;
[Hide, *Spectral Gap for Weil–Petersson Random Surfaces with Cusps*](https://academic.oup.com/imrn/article/2023/20/17411/6765005), §4.4 and the proof of Lemma 4.7;
[Martelli, *Hyperbolic geometry, surfaces, and 3-manifolds*](https://web.dm.unipi.it/martelli/didattica/matematica/2014/Hyperbolic%20geometry.pdf), version dated 2013-12-18.

Martelli, Ch. 2, Proposition 4.1 (p. 45), gives the disk area `2π(cosh r−1)`;
Ch. 4, Proposition 1.1 (p. 69), gives the injectivity radius in terms of deck-transformation displacement;
Proposition 1.14 (p. 72) gives the correspondence between axes and geodesics.
The short-collar area `2l/sinh(l/2)` is a general consequence of integrating the standard collar metric.
The collar facts used here allow cusps; a global counting lemma restricted to closed surfaces is not a substitute.

Ch. 4, Proposition 2.20 (p. 81), treats doubling along compact geodesic boundary while retaining cusp ends.
The Gauss–Bonnet statement in Ch. 5, Theorem 1.3 (p. 84), concerns compact surfaces.
For a surface of finite area with cusps, first truncate by horocycles and then let their lengths tend to zero.
Ch. 4, Proposition 1.7 (p. 71), supplies the corresponding cusp area. The noncompact version is thus an explicit consequence of truncation.

The doubling interface requires actual embeddings, local isometries, compatibility of geodesic lengths and traces, and preservation of primitivity.
When the surface has no boundary, use the original complete surface; two disconnected copies do not supply the required complete surface.
These inputs do not directly provide the paper's uniform primitive-curve counting bound.

</details>

<a id="regular-neighborhood"></a>

<details>
<summary>Regular neighborhoods of finite embedded graphs</summary>

The source is [Lazarus–de Mesmay, *Surfaces and embedded graphs*](https://pagesperso.g-scop.grenoble-inp.fr/~lazarusf/Enseignement/compuTopo3.pdf), version dated 2017-10-05, §1.1 (p. 2) and §2 (pp. 8–9, Figure 9).
The vertex-disk and edge-band construction allows loops and multiple edges. Neighborhood boundaries correspond to the `rho*iota` cycles of the rotation system.

The interface requires a compact, regular closed neighborhood of an actual embedded graph, with the graph in its interior and a homeomorphism between the actual and combinatorial boundaries.
It requires a strong deformation retraction fixing the graph support, whose restriction to the boundary agrees with the actual boundary walk.
Numerical genus bounds, length bounds, and the paper's recording conclusions are not fields of this interface.

The source's global convention is that surfaces are compact. To apply the construction to a surface with cusps, use compactness of the finite graph support
and perform the same disk-and-band construction in finitely many local charts around that support.
This is a local consequence, rather than a direct application of the global classification of compact surfaces to a noncompact surface.

</details>

<a id="surface-euler"></a>

<details>
<summary>Finite cell models and Euler characteristics</summary>

[Hatcher, *Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Theorem 2.44, pp. 146–147,
gives the Euler characteristic of finite CW complexes and its homotopy invariance.
`SurfaceCellularEulerClassics` applies this fact to an actual finite two-dimensional cell model of the given surface; cell counts are `Nat.card` of the actual cell types.

For a hyperbolic surface of finite area with compact geodesic boundary, one must also use Martelli's surface classification, cusp truncation, and Gauss–Bonnet, cited in the preceding section,
to identify this homotopy invariant with `-area/(2*pi)` and the surface's `negativeEuler`.
Hatcher's theorem itself has no conclusion about hyperbolic area or cusp labels.
The interface does not directly provide the cell model of a particular filling region in the paper or its edge budget; those are separate constructions with their own proofs.

</details>

<a id="straightening"></a>

<details>
<summary>Closed-loop straightening and annuli</summary>

The source is [Farb–Margalit, *A Primer on Mapping Class Groups*, Version 5.0](https://pagine.dm.unipi.it/~a019210/Farb%20Magalit_Primer%20on%20Teichmuller%20theory.pdf), the authors' January 2011 draft.
Page 18 allows cusps and boundaries; p. 22 discusses classes on complete hyperbolic surfaces of finite area.

`ClosedLoop` is an actual continuous map from an interval with equal endpoints. Its length is metric total variation.
`PositiveHomotopyLength` means that the lengths of all actual closed loops in the same free homotopy class have a common positive lower bound.
This excludes null-homotopic classes and peripheral cusp classes that can be shortened arbitrarily.

| Classical input | Location and scope |
| --- | --- |
| Primitive geodesic representatives of simple classes and their uniqueness | Proposition 1.3, pp. 25–26; Proposition 1.4, pp. 27–28 |
| Geodesic representatives minimize length | A metric consequence of the axis-and-lift construction; nonrectifiable representatives have infinite total variation |
| Simple and disjoint representatives | Proposition 1.6, pp. 28–29; Corollary 1.9, p. 34; the Multicurves paragraph on p. 35 |
| Actual embedded annuli between disjoint, freely homotopic, essential simple curves | The second half of the proof of Proposition 1.10, pp. 35–36 |

All these fields use the same complete surface, explicitly requiring `surface.domain = univ`.
The annulus is an actual continuous injection; its two boundary curves agree with the given curves through recorded reparameterizations.
This does not automatically show that a network avoids the annulus, or supply the paper's particular filling and recording steps.

</details>

<a id="complement"></a>

<details>
<summary>Disks and cusp ends bounded by simple closed loops</summary>

[ Marden–Richards–Rodin, “On the regions bounded by homotopic curves”](https://msp.org/pjm/1966/16-2/pjm-v16-n2-p13-s.pdf),
*Pacific J. Math.* 16(2) (1966), pp. 337–339, applies to orientable compact or noncompact surfaces.
Assertion (i) and its proof show that a null-homotopic simple closed loop bounds an actual embedded closed disk; assertion (ii) treats annuli between homotopic curves.

Together with Farb–Margalit's classification of axial and parabolic classes and standard cusp geometry, this implies:
every actual simple closed loop on a complete surface of finite area either has a positive homotopy-length lower bound, bounds an actual closed disk, or bounds an actual closed embedded cusp half-cylinder.
The interiors of the disk and half-cylinder must be open in the surface, with frontier exactly the original loop. The closed embedding must not omit interior points or other cusps.

The cusp-end conclusion follows by choosing a distant standard cusp cross-section and attaching the compact annulus between it and the original loop.
This is an explicit general consequence, not a claim that the source states the Lean fields verbatim.
The trichotomy does not provide compatible filling choices for multiple network boundaries, length budgets, or multiplicity bounds.

</details>

<a id="nef"></a>

<details>
<summary>Nef classes and mixed intersections</summary>

- [Arbarello–Cornalba, alg-geom/9406008](https://arxiv.org/pdf/alg-geom/9406008), §1, pp. 3–6: equation (1.5) distinguishes logarithmic from nonlogarithmic κ classes; equation (1.6) concerns ampleness of logarithmic κ₁; equation (1.7) is the pushforward formula for powers of ψ under the forgetful map. The logarithmic κ₁ for `g≥2, n=1` is used here; the nonlogarithmic version cannot replace it.
- [Keel, math/9901149](https://arxiv.org/pdf/math/9901149), Theorem 0.4, p. 3: the nefness and bigness assertions for the logarithmic relative dualizing class of the universal stable curve are not restricted to positive characteristic. Only the additional semiampleness conclusion has that restriction. No semiampleness conclusion in characteristic zero is used here.
- [Boucksom–Favre–Jonsson, math/0608260v2](https://arxiv.org/pdf/math/0608260), Theorem 2.15, p. 15: mixed intersection inequalities and log-concavity for nef classes on projective varieties.

Applying these facts to Deligne–Mumford moduli spaces also requires finite-level covers, pullback to resolutions, preservation of nefness, and scaling of integrals by a common positive degree.
These obligations are part of the exact scope of the classical inputs. A theorem about projective varieties does not by itself construct the required instance on moduli space.
The interface uses the general Teissier laws for nef classes and the properties of ψ and logarithmic κ. The paper's numerical adjacent-ratio and error conclusions are not interface fields.

</details>
