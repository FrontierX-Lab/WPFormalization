# Remaining infrastructure

The goal is to turn the current proofs under classical premises into complete proofs about the mathematical objects in the paper.
This requires completing the proofs in [Classical results](CLASSICAL_RESULTS.md), constructing the intended objects, and connecting them to the existing proofs of the [paper targets](TARGETS.md).
The obligations for each group of classical premises are listed once below.

## Work overview

| Area | Required outcome |
| --- | --- |
| [Constructing intersection theory and moduli spaces](#foundation-intersection) | Construct Deligne–Mumford moduli spaces, psi and logarithmic kappa classes, and integration. Prove the classical identities and mixed intersection transform, and provide objects satisfying the existing intersection interfaces. |
| [Classical intersection formulas](#foundation-intersection-identities) | Complete the one-point and two-point intersection estimates, the KdV and Itzykson–Zuber identities, and the required uniqueness and normalization transfers. |
| [WP measures, volume formulas, and classical volume estimates](#foundation-wp-volume) | Construct moduli spaces with boundaries or cusps and their WP measures. Prove the volume polynomial, fixed-cusp and fixed-genus asymptotics, and the required classical volume bounds. Identify the geometric volumes with the existing numerical model. |
| [Special functions and complex analysis](#foundation-analysis) | Complete the Gamma/Binet remainder estimates, Bessel zero results, and the precise classical versions of the analytic implicit-function, Pringsheim, Rouché, and Hadamard theorems. |
| [Painlevé I analysis](#foundation-painleve) | Construct solutions and Borel data with the specified normalization. Prove the classical large-order asymptotics, contour and fixed-order jump formulas, and branch continuation. |
| [Hyperbolic surfaces and closed geodesics](#foundation-hyperbolic) | Construct hyperbolic quotient surfaces of finite area, closed geodesics, collars, and doubled surfaces. Prove the precise measurability, primitivity, and boundary-representative properties required. |
| [Topology of surfaces and embedded graphs](#foundation-topology) | Complete the results on regular neighborhoods, curve straightening, annuli and complementary regions, finite cell structures, and fundamental groups. Connect them to the actual surface objects. |
| [Multicurve cutting, filling, and pairs of pants](#foundation-cuts) | Construct cut components and filling subsurfaces. Prove the classical results on labeled multicurve integration, measurable counts, families of pairs of pants, and their deformations. |
| [Tight-boundary geometry and volumes](#foundation-tight) | Construct homotopy classes after capping, tight-boundary regions, and their measurable structures. Prove the Budd–Zonneveld transform and the Budd–Lions cutting integrals and deterministic geometry results. |
| [Laplace spectra and local variational estimates](#foundation-spectrum) | Construct spectra, multiplicities, and measurable eigenvalue events on the actual surfaces. Prove the required estimates for test functions on pairs of pants, min–max, and Cheeger/Buser inequalities. |
| [Point measures, Poisson processes, and probability limits](#foundation-probability) | Complete the measurable and topological structures on point-measure spaces, existence of Poisson processes, moment and Laplace-functional formulas, count criteria, and continuous-mapping results. |

<a id="foundation-intersection"></a>

## Constructing intersection theory and moduli spaces

Construct Deligne–Mumford moduli spaces, psi and logarithmic kappa classes, and integration. Prove the classical identities and mixed intersection transform, and provide objects satisfying the existing intersection interfaces.

<details>
<summary>View individual obligations</summary>

<a id="task-int-psi"></a>

- [ ] **[Classical identities for psi intersection numbers (INT-PSI)](CLASSICAL_RESULTS.md#input-int-psi)**

  Construct the geometric psi correlators and prove they satisfy exactly the listed fields.

<a id="task-int-coh"></a>

- [ ] **[Cohomology classes and integration on moduli spaces (INT-COH)](CLASSICAL_RESULTS.md#input-int-coh)**

  Construct the DM orbifold/stack and even cohomology, psi/log-kappa classes, integration and Wolpert identity.

<a id="task-int-kmz"></a>

- [ ] **[The mixed kappa–psi intersection transform (INT-KMZ)](CLASSICAL_RESULTS.md#input-int-kmz)**

  Prove the pure identification and KMZ mixed transform for the actual geometric family.

<a id="task-int-higher-kappa"></a>

- [ ] **[Higher logarithmic kappa intersections (INT-HIGHER-KAPPA)](CLASSICAL_RESULTS.md#input-int-higher-kappa)**

  Construct actual DM stack/family/log-kappa classes and same-P realization; prove generic Schur transform via KMZ/MZ, ample kappa1 positivity, and mixed nonnegativity on Cartesian powers of the original proper flat universal curve using base change/projection/nef pullback. Formalize finite projective positive-degree cover and orbifold/stack transfer; do not replace the Cartesian fiber power by distinct-marked moduli. No concrete instance currently exists.

<a id="task-int-nef"></a>

- [ ] **[Nef intersection inequalities and their realization on moduli spaces (INT-NEF)](CLASSICAL_RESULTS.md#input-int-nef)**

  Construct the canonical geometric realization and DVV uniqueness transfer, realize log-kappa/psi Cartier classes on compact projective covers, formalize their ample/nef theorems and generic Teissier, prove cover/resolution/orbifold projection factors, then replace this sole external existence root without importing the paper C7 conclusion.

</details>

<a id="foundation-intersection-identities"></a>

## Classical intersection formulas

Complete the one-point and two-point intersection estimates, the KdV and Itzykson–Zuber identities, and the required uniqueness and normalization transfers.

<details>
<summary>View individual obligations</summary>

<a id="task-int-one"></a>

- [ ] **[The one-point psi intersection formula (INT-ONE)](CLASSICAL_RESULTS.md#input-int-one)**

  Prove from the classical recursion or transfer a geometric one-point formula using uniqueness. This transfer is part of the deferred external proof, not a verified Lean implication.

<a id="task-int-two"></a>

- [ ] **[An upper bound for two-point psi intersections (INT-TWO)](CLASSICAL_RESULTS.md#input-int-two)**

  Prove uniqueness/normalization transfer and the published two-point inequality, then eliminate this external sorry.

<a id="task-int-kdv"></a>

- [ ] **[The first integrated KdV identity for pure psi intersections (INT-KDV)](CLASSICAL_RESULTS.md#input-int-kdv)**

  Derive the integrated classical KdV identity from the genuine Witten–Kontsevich tau function, including coefficient extraction and DVV uniqueness transfer to arbitrary P; no unproved integration-constant removal is inferred from the differential equation alone.

<a id="task-pi-iz"></a>

- [ ] **[The endpoint identity for intersections and Painlevé coefficients (PI-IZ)](CLASSICAL_RESULTS.md#input-pi-iz)**

  Prove the classical IZ identity from KW theory and the uniqueness/normalization transfers.

</details>

<a id="foundation-wp-volume"></a>

## WP measures, volume formulas, and classical volume estimates

Construct moduli spaces with boundaries or cusps and their WP measures. Prove the volume polynomial, fixed-cusp and fixed-genus asymptotics, and the required classical volume bounds. Identify the geometric volumes with the existing numerical model.

<details>
<summary>View individual obligations</summary>

<a id="task-wp-poly"></a>

- [ ] **[The intersection polynomial for WP volumes (WP-POLY)](CLASSICAL_RESULTS.md#input-wp-poly)**

  Construct labeled geodesic-boundary hyperbolic moduli, its measurable orbifold symplectic measure, finiteness, and classical polynomial law.

<a id="task-wp-mz-fixed"></a>

- [ ] **[WP volume asymptotics with a fixed number of cusps (WP-MZ-FIXED)](CLASSICAL_RESULTS.md#input-wp-mz-fixed)**

  Formalize the classical geometric fixed-cusp theorem or its leading consequence, construct/identify the canonical intersection numbers, and prove the DVV uniqueness plus KMZ/Wolpert normalization transfer. Remove this external root without assuming the new Zograf constant value. Formalize its fixed-n=0 first correction with the same unknown universal normalization, and the exact coefficient stated in Remark1.3.

<a id="task-wp-mz-fixed-genus"></a>

- [ ] **[Volume asymptotics at fixed genus with increasing cusp count (WP-MZ-FIXED-GENUS)](CLASSICAL_RESULTS.md#input-wp-mz-fixed-genus)**

  Formalize fixed-genus classical asymptotic, the Bessel singularity normalization, DVV uniqueness/KMZ/Wolpert transfer and the elementary logarithmic corollary.

<a id="task-wp-shen-wu-pants"></a>

- [ ] **[A second-moment lower bound for short-pants counts (WP-SHEN-WU-PANTS)](CLASSICAL_RESULTS.md#input-wp-shen-wu-pants)**

  Formalize published exact integration and first/second moment lower bound for actual short-pants count, including finite volume and limits; construct actual G/H instance.

<a id="task-wp-sw-critical-volume"></a>

- [ ] **[General upper bounds and critical-range lower bounds for WP volumes (WP-SW-CRITICAL-VOLUME)](CLASSICAL_RESULTS.md#input-wp-sw-critical-volume)**

  Prove published volume estimates and fixed-A uniformity, handle h=1 finite types, formalize DVV uniqueness/KMZ/Wolpert transfer and construct the actual geometric instance.

<a id="task-wp-genus0-boundary"></a>

- [ ] **[Comparison of genus-zero WP volumes with boundaries (WP-GENUS0-BOUNDARY)](CLASSICAL_RESULTS.md#input-wp-genus0-boundary)**

  Prove the published generic volume coefficient comparison from classical Mirzakhani recursion or instantiate/transfer normalized actual WP intersection theory using DVV uniqueness, then eliminate this one exact root. No new planar count, moment, tail or asymptotic is a deferred assumption.

</details>

<a id="foundation-analysis"></a>

## Special functions and complex analysis

Complete the Gamma/Binet remainder estimates, Bessel zero results, and the precise classical versions of the analytic implicit-function, Pringsheim, Rouché, and Hadamard theorems.

<details>
<summary>View individual obligations</summary>

<a id="task-sf-gamma-ratio"></a>

- [ ] **[Gamma ratio estimates with fixed parameter shifts (SF-GAMMA-RATIO)](CLASSICAL_RESULTS.md#input-sf-gamma-ratio)**

  Derive from a full real-Gamma Stirling/Binet theorem; Mathlib currently supplies factorial Stirling and exact Gamma algebra.

<a id="task-sf-gamma-stirling"></a>

- [ ] **[Stirling remainder bounds for the real Gamma function (SF-GAMMA-STIRLING)](CLASSICAL_RESULTS.md#input-sf-gamma-stirling)**

  Extend/reuse factorial Stirling to real Gamma via Binet or Euler–Maclaurin with a first-order remainder.

<a id="task-sf-binet"></a>

- [ ] **[The Binet remainder and Laplace representation for log Gamma (SF-BINET)](CLASSICAL_RESULTS.md#input-sf-binet)**

  Prove the Binet integral remainder or Euler–Maclaurin formula, replacing only this mature external gap. Prove the exact digamma/Frullani integrated representation with joint absolute integrability, or derive it from a native Binet theorem.

<a id="task-bessel-j0"></a>

- [ ] **[Zeros of the Bessel J0 function (BESSEL-J0)](CLASSICAL_RESULTS.md#input-bessel-j0)**

  Formalize classical Bessel J0 spectral/energy theory or reuse a compatible Bessel library; the kernel deformation proof remains a separate paper obligation.

<a id="task-gen-analytic-ift"></a>

- [ ] **[Analytic implicit functions and convergence of formal branches (GEN-ANALYTIC-IFT)](CLASSICAL_RESULTS.md#input-gen-analytic-ift)**

  Formalize the convergent MvPowerSeries-to-analytic-germ/Taylor-composition bridge, generic invertible-Jacobian formal uniqueness, and the classical holomorphic IFT implication using Mathlib inverse APIs.

<a id="task-gen-pringsheim"></a>

- [ ] **[Real-axis singularities of nonnegative power series (GEN-PRINGSHEIM)](CLASSICAL_RESULTS.md#input-gen-pringsheim)**

  Formalize Pringsheim’s positive real singularity theorem and the generic meromorphic reciprocal radius/nearest-zero corollary, reusing Mathlib analytic/power-series APIs.

<a id="task-gen-rouche"></a>

- [ ] **[Counting complex zeros with multiplicity (GEN-ROUCHE)](CLASSICAL_RESULTS.md#input-gen-rouche)**

  Formalize the argument principle/Rouche multiplicity count and its finite prescribed-zero corollary with Mathlib analytic order APIs.

<a id="task-gen-hadamard"></a>

- [ ] **[Product factorization of entire functions of finite order (GEN-HADAMARD)](CLASSICAL_RESULTS.md#input-gen-hadamard)**

  Formalize finite-order Hadamard factorization and the genus0 specialization, including absolute/unconditional product convergence and normalization at zero.

</details>

<a id="foundation-painleve"></a>

## Painlevé I analysis

Construct solutions and Borel data with the specified normalization. Prove the classical large-order asymptotics, contour and fixed-order jump formulas, and branch continuation.

<details>
<summary>View individual obligations</summary>

<a id="task-pi-leading"></a>

- [ ] **[Classical large-order asymptotics of Painlevé coefficients (PI-LEADING)](CLASSICAL_RESULTS.md#input-pi-leading)**

  Implement normalized tritronquee theory or transplant its classical large-order proof, with exact Stokes convention.

<a id="task-pi-contour"></a>

- [ ] **[Contour representations and fixed-order jumps for Painlevé I (PI-CONTOUR)](CLASSICAL_RESULTS.md#input-pi-contour)**

  Construct the normalized tritronquee meromorphic functions and prove the classical sector/fixed-order/contour statements, including their exact source normalizations.

<a id="task-pi-borel"></a>

- [ ] **[The Borel representation of Painlevé I (PI-BOREL)](CLASSICAL_RESULTS.md#input-pi-borel)**

  Formalize classical PI Borel continuation, local singularity and generalized transseries resummation, including ordinary fixed-ray continuation and parameter limits.

</details>

<a id="foundation-hyperbolic"></a>

## Hyperbolic surfaces and closed geodesics

Construct hyperbolic quotient surfaces of finite area, closed geodesics, collars, and doubled surfaces. Prove the precise measurability, primitivity, and boundary-representative properties required.

<details>
<summary>View individual obligations</summary>

<a id="task-hyp-curves"></a>

- [ ] **[Curves on hyperbolic surfaces and measurable length counts (HYP-CURVES)](CLASSICAL_RESULTS.md#input-hyp-curves)**

  Construct geodesic/free-homotopy classes on actual moduli, local finiteness with cusps, continuous length and moduli descent; identify planar topology and prove count measurability.

<a id="task-hyp-surface-quotient"></a>

- [ ] **[Hyperbolic quotient surfaces and primitive geodesics (HYP-SURFACE-QUOTIENT)](CLASSICAL_RESULTS.md#input-hyp-surface-quotient)**

  Construct actual deck quotients, primitive axes/conjugacy classes, finite length catalog, area/topology and cusped Gauss-Bonnet; instantiate same G/H ambient model. No cardinal estimate or G3 recording is an input.

<a id="task-hyp-collar"></a>

- [ ] **[Simplicity and disjointness of short primitive geodesics (HYP-COLLAR)](CLASSICAL_RESULTS.md#input-hyp-collar)**

  Construct the actual collars and prove their disjointness, the short primitive simplicity theorem including finite-area cusps, and identify the same H/T geometric objects.

<a id="task-hyp-local-packing"></a>

- [ ] **[Local geometry of hyperbolic disks and thin collars (HYP-LOCAL-PACKING)](CLASSICAL_RESULTS.md#input-hyp-local-packing)**

  Formalize disk area, injectivity radius, Margulis/collar classification including cusps, embedded collars and their exact areas on the same actual quotient. Do not replace the locally proved net or loop bound by an equivalent axiom.

<a id="task-hyp-doubling"></a>

- [ ] **[Doubling surfaces along geodesic boundaries (HYP-DOUBLING)](CLASSICAL_RESULTS.md#input-hyp-doubling)**

  Construct and verify actual double (or identity for empty boundary), compatible point/deck primitive inclusions, local isometry and area factor. Later embedded filled-piece inclusion into ambient surface remains a separately audited geometric bridge.

<a id="task-hyp-arc-endpoint"></a>

- [ ] **[Local comparison of geodesic arc endpoints (HYP-ARC-ENDPOINT)](CLASSICAL_RESULTS.md#input-hyp-arc-endpoint)**

  Formalize the local hyperbolic arc/Margulis endpoint inequality on the actual quotient, with transversality from distinct simple geodesic uniqueness and monotonicity of coth. No global G3 estimate is deferred.

<a id="task-hyp-bordered-loop"></a>

- [ ] **[Curve straightening on convex bordered hyperbolic surfaces (HYP-BORDERED-LOOP)](CLASSICAL_RESULTS.md#input-hyp-bordered-loop)**

  Prove five generic axis/convex-domain facts, including actual continuous loop variation bounds and primitive/conjugacy/inversion identifications for actual models.

<a id="task-hyp-primitive-boundary"></a>

- [ ] **[Intrinsic primitive traces and boundary uniqueness (HYP-PRIMITIVE-BOUNDARY)](CLASSICAL_RESULTS.md#input-hyp-primitive-boundary)**

  Prove trace determines primitive unoriented class and boundary tangency uniqueness in genuine geodesic-boundary quotient. Exercise1.11 is framework, not a claimed proved exact API.

<a id="task-hyp-peripheral-axial"></a>

- [ ] **[Axial geodesics in cusp ends and compact annuli (HYP-PERIPHERAL-AXIAL)](CLASSICAL_RESULTS.md#input-hyp-peripheral-axial)**

  Construct actual cusp-tail parabolic classification and cyclic annulus fundamental group. Primitive axial class in annulus forces exponent±1; cusp parabolic subgroup has no axial element. Discharge explicit two-field parameter.

</details>

<a id="foundation-topology"></a>

## Topology of surfaces and embedded graphs

Complete the results on regular neighborhoods, curve straightening, annuli and complementary regions, finite cell structures, and fundamental groups. Connect them to the actual surface objects.

<details>
<summary>View individual obligations</summary>

<a id="task-top-regular-neighborhood"></a>

- [ ] **[Regular neighborhoods of finite graphs in surfaces (TOP-REGULAR-NEIGHBORHOOD)](CLASSICAL_RESULTS.md#input-top-regular-neighborhood)**

  Construct local surface charts, oriented rotation, disks/bands, actual frontier homeomorphism and parametrized strong deformation retraction. No actual instance yet. Exact field review docs/CLASSICAL_RESULTS.md#regular-neighborhood.

<a id="task-top-surface-euler"></a>

- [ ] **[Finite CW decompositions and Euler characteristics of surfaces (TOP-SURFACE-EULER)](CLASSICAL_RESULTS.md#input-top-surface-euler)**

  Prove finite CW Euler/homotopy invariance, compact cusp-core homotopy model and Gauss–Bonnet identification for actual B. No actual instance. Exact field review docs/CLASSICAL_RESULTS.md#surface-euler.

<a id="task-top-loop-straightening"></a>

- [ ] **[Geodesic straightening of closed-loop homotopy classes (TOP-LOOP-STRAIGHTENING)](CLASSICAL_RESULTS.md#input-top-loop-straightening)**

  Construct loop lifts, primitive axis, free-homotopy conjugacy dictionary, total-variation length comparison, simple/minimal-position results for actual quotient. No actual instance. Full ledger docs/CLASSICAL_RESULTS.md#straightening.

<a id="task-top-simple-annulus"></a>

- [ ] **[Annuli between disjoint homotopic simple closed curves (TOP-SIMPLE-ANNULUS)](CLASSICAL_RESULTS.md#input-top-simple-annulus)**

  Construct universal-cover strip, cyclic quotient embedded compact annulus, boundary parametrization and reparametrization. No actual instance.

<a id="task-top-simple-complement"></a>

- [ ] **[Simple closed curves, disks, and cusp ends (TOP-SIMPLE-COMPLEMENT)](CLASSICAL_RESULTS.md#input-top-simple-complement)**

  Prove actual deck-class trichotomy, Jordan–Schoenflies disk embedding, annulus-to-far-cusp gluing and proper half-cylinder embedding with actual frontier semantics. No actual instance. Source/type ledger docs/CLASSICAL_RESULTS.md#complement.

<a id="task-top-cyclic-interval"></a>

- [ ] **[Topology of finite interval gluings (TOP-CYCLIC-INTERVAL)](CLASSICAL_RESULTS.md#input-top-cyclic-interval)**

  Construct the explicit inverse [j,s]↦[(j+s)/m], prove endpoint compatibility, continuity and bijectivity with compact-Hausdorff descent using Mathlib quotient APIs. Eliminate this explicit generic parameter; no paper estimates are supplied.

<a id="task-top-planar-jordan"></a>

- [ ] **[Planar Jordan–Schoenflies extension (TOP-PLANAR-JORDAN)](CLASSICAL_RESULTS.md#input-top-planar-jordan)**

  Formalize the planar Jordan–Schoenflies extension theorem or reuse a compatible formalization; supply exact extension on the circle. Keep later finite-puncture and paper-specific classification separate.

<a id="task-top-planar-regions"></a>

- [ ] **[Coordinates on planar annuli and punctured disks (TOP-PLANAR-REGIONS)](CLASSICAL_RESULTS.md#input-top-planar-regions)**

  Prove general planar annulus theorem plus relative boundary parametrization using Jordan–Schoenflies; prove exact punctured-disk polar homeomorphism. Supply the generic parameter without importing Critical paper modules.

<a id="task-top-graph-pi1"></a>

- [ ] **[Fundamental groups of finite connected graphs (TOP-GRAPH-PI1)](CLASSICAL_RESULTS.md#input-top-graph-pi1)**

  Formalize graph maximal trees, actual based-edge-loop free basis and finitecard upper bound using MathlibCW/FundamentalGroup APIs; actualNetworkCW and resulting paper budgets remain local.

<a id="task-top-surface-pi1"></a>

- [ ] **[Fundamental groups of orientable hyperbolic surfaces of finite area (TOP-SURFACE-PI1)](CLASSICAL_RESULTS.md#input-top-surface-pi1)**

  Construct actualfinite-type surface presentation/abelianization or graphretraction and correspondingrank lower bound; prove actualGaussBonnet Euler agrees with topological Euler and discharge genericparameter without paperrecording assumptions.

</details>

<a id="foundation-cuts"></a>

## Multicurve cutting, filling, and pairs of pants

Construct cut components and filling subsurfaces. Prove the classical results on labeled multicurve integration, measurable counts, families of pairs of pants, and their deformations.

<details>
<summary>View individual obligations</summary>

<a id="task-hyp-multicurve-integration"></a>

- [ ] **[Cutting and integration for labeled multicurves (HYP-MULTICURVE-INTEGRATION)](CLASSICAL_RESULTS.md#input-hyp-multicurve-integration)**

  Construct mapping-class orbits and actual cut surfaces for G/H, prove change-of-coordinates classification/realization and planar-side binding, derive the exact orientation coefficient and Mirzakhani integration via Fenchel–Nielsen coordinates with orbifold stabilizers.

<a id="task-mc-count-borel"></a>

- [ ] **[Measurability of unordered multicurve observables (MC-COUNT-BOREL)](CLASSICAL_RESULTS.md#input-mc-count-borel)**

  Construct countable marked curve labels, continuous lengths, proper MCG action/local orbifold charts and Borel descent for the actual simultaneous G/H/T. Prove the generic unordered observable measurable, including finite permutation existential quantification. No actual instance currently constructed.

<a id="task-mc-cut-restriction"></a>

- [ ] **[Compatibility of multicurve cutting with restriction (MC-CUT-RESTRICTION)](CLASSICAL_RESULTS.md#input-mc-cut-restriction)**

  Construct actual surface cut and gluing maps for the same mapping class orbits, prove restriction membership and component/genus naturality from oriented-surface classification. No actual instance exists.

<a id="task-mc-cut-components"></a>

- [ ] **[Geometric realization of cut components (MC-CUT-COMPONENTS)](CLASSICAL_RESULTS.md#input-mc-cut-components)**

  Construct actual cut pieces/complement component equivalence and exact genus/cusp/half-side identifications for simultaneous A/H/T. No actual instances; no G3 network bound, collapse procedure, marked classification or expectation is deferred. Construct this same actual cut-type topological homeomorphism and exact boundary identification; filled-network selection/classification/graph estimates remain local. Prove actual models complete the same intrinsic path-metric open surface; uniqueness extends the interior identity, finite-distance added boundary points are precisely intrinsic boundaries, and complete cusps add none. Prove the inverse finite-type label recognition for the genuine cut object from topological invariance of genus, compact boundary components and punctured ends; construct the companion alongside the SAME actual R. Construct the coherent all-actual-cut family and SAME Hide-to-cut companions from the classical geometric creators; no additional mathematical theorem is asserted by the data packaging.

<a id="task-hyp-intrinsic-pieces"></a>

- [ ] **[Intrinsic completions of subsurfaces and primitive curves (HYP-INTRINSIC-PIECES)](CLASSICAL_RESULTS.md#input-hyp-intrinsic-pieces)**

  Construct the actual intrinsic completion/convex covering and root-closed primitive projection/lifting, preserve two intrinsic boundary circles when ambient traces coincide, instantiate simultaneous same-H/T semantic model. No actual instance yet. Also prove true completion frontier/area semantics (local volume form, interior embedding, geodesic boundary area0, proper cusp ends) and same-or-disjoint projected actual boundaries. No selected cut component, Euler inequality, filled recording or multiplicity estimate is supplied by companions.

<a id="task-hyp-single-filling"></a>

- [ ] **[The filling subsurface of one nonsimple geodesic (HYP-SINGLE-FILLING)](CLASSICAL_RESULTS.md#input-hyp-single-filling)**

  Construct actual Hide X(gamma) with intrinsic boundary copies retained; prove containment, boundary/area bounds and same-choice intrinsic beta plus actual simple-loop filling consequence from disk/peripheral-cylinder complementary regions. Build S and its refinement together for actual ambient models. No actual instance is yet constructed. Implement generic bordered RN surgery inside the actual closed convex quotient, with surviving formal boundary semantics and perimeter bound; actual positiveboundary and canonical waist support remain local paper proofs. Construct the same canonical S with this minimum supporting-image companion; prove the comparison using the old RN/convex-hull construction, rather than inferring it from the weak InteriorFilling corollary or numeric budgets. Construct the coherent all-actual-cut family and SAME Hide-to-cut companions from the classical geometric creators; no additional mathematical theorem is asserted by the data packaging. Construct full disk/boundary-cylinder/cusp-cylinder complement coordinates for the same actual Hide piece and its intrinsic lifted curve. Retain ambient proper-end embedding, instead of identifying the weak simple-loop consequence with full filling.

<a id="task-hyp-pants-family"></a>

- [ ] **[Marked families of pairs of pants with two cusps (HYP-PANTS-FAMILY)](CLASSICAL_RESULTS.md#input-hyp-pants-family)**

  Construct actual marked pants via ideal/right-angled hexagons, convex covering, topological realization, primitive/deck marking, boundary realization and double. No actual instance exists yet.

<a id="task-hyp-pants-deformation"></a>

- [ ] **[Metric comparison under deformations of pairs of pants (HYP-PANTS-DEFORMATION)](CLASSICAL_RESULTS.md#input-hyp-pants-deformation)**

  Construct Bishop maps in the same marking including two punctures, reflect across geodesic boundary, prove the all-geodesic Wolpert length inequality and apply to exact primitive catalog. No actual instance yet.

<a id="task-hyp-pants-uniqueness"></a>

- [ ] **[Metric uniqueness of pairs of pants with two cusps (HYP-PANTS-UNIQUENESS)](CLASSICAL_RESULTS.md#input-hyp-pants-uniqueness)**

  Prove actual geometric pants uniqueness and induced geodesic-class transport with boundary compatibility; instantiate for constructed models. No actual instance yet.

<a id="task-hyp-finite-support"></a>

- [ ] **[Convex supporting subsurfaces for finite geodesic sets (HYP-FINITE-SUPPORT)](CLASSICAL_RESULTS.md#input-hyp-finite-support)**

  Construct the actual graph subgroup/lift, regular neighborhood fill-and-tighten and convex-hull support; prove exact hull and minimality statements and genuine region/boundary semantics. No instance for arbitrary partial records is asserted. General construction only, not paper estimates. Construct these companions with the actualsupport/RN creators, including all formal duplicate sides and actualcarrier pi1 surjection. Assemble these four existing construction companions coherently on the same actual tuple network, RN and SP supports; no additional mathematical estimate or existence for arbitrary partial objects.

<a id="task-hyp-pants-figure-eight"></a>

- [ ] **[Figure-eight curves in hyperbolic pairs of pants (HYP-PANTS-FIGURE-EIGHT)](CLASSICAL_RESULTS.md#input-hyp-pants-figure-eight)**

  Construct the two parabolic peripheral generators in the actual deck group; prove their product inverse word primitive and nonperipheral, and derive its length from the SL₂ trace identity. Transfer to the existing full primitive catalog.

</details>

<a id="foundation-tight"></a>

## Tight-boundary geometry and volumes

Construct homotopy classes after capping, tight-boundary regions, and their measurable structures. Prove the Budd–Zonneveld transform and the Budd–Lions cutting integrals and deterministic geometry results.

<details>
<summary>View individual obligations</summary>

<a id="task-tight-bz"></a>

- [ ] **[Tight-boundary geometry and the moment transform (TIGHT-BZ)](CLASSICAL_RESULTS.md#input-tight-bz)**

  Construct actual simple cycles, capping and protected-tight locus on G, prove measurability and the generic classical BZ formal transform with dilaton resummation, including all geometric/psi normalization transfers. No concrete instance currently constructed.

<a id="task-hyp-tight-curves"></a>

- [ ] **[Homotopy classes of closed geodesics after capping (HYP-TIGHT-CURVES)](CLASSICAL_RESULTS.md#input-hyp-tight-curves)**

  Construct all closed geodesic objects and capped classes on actual hyperbolic moduli, simpleCycle and same-H identifications. No concrete realization has been constructed.

<a id="task-tight-cut-topology"></a>

- [ ] **[Orbit classification of ordered tight multicurves (TIGHT-CUT-TOPOLOGY)](CLASSICAL_RESULTS.md#input-tight-cut-topology)**

  Construct actual mapping class action, orbit partition and classification, cut surfaces, edge incidences and labels. This supplies no genus/cusp-uniform estimate and no geometric instance yet.

<a id="task-bl-tight-integration"></a>

- [ ] **[Integration over restricted regions for tight multicurves (BL-TIGHT-INTEGRATION)](CLASSICAL_RESULTS.md#input-bl-tight-integration)**

  Formalize original cut/twist symplectic integration, actual source orbifold normalization including genus1, assignment partition and measurability. No concrete instance yet.

<a id="task-bl-tight-geometry"></a>

- [ ] **[Extension and general-position properties of tight geodesic families (BL-TIGHT-GEOMETRY)](CLASSICAL_RESULTS.md#input-bl-tight-geometry)**

  Construct/prove pointwise ribbon-subsurface tightening, unique minimizers away from no-ties exception, shortest-tight simplicity and classical WP-null equal-length locus. No concrete instance yet.

<a id="task-hyp-tight-borel"></a>

- [ ] **[Countable geodesic labels and measurable moduli quotients (HYP-TIGHT-BOREL)](CLASSICAL_RESULTS.md#input-hyp-tight-borel)**

  Construct marked hyperbolic Teichmuller spaces, countable free-homotopy labels, actual geodesic equivalences/capping relations and Borel lengths; prove proper MCG quotient/orbifold measurable descent for simultaneous G/T/H/Q. No instance currently constructed.

</details>

<a id="foundation-spectrum"></a>

## Laplace spectra and local variational estimates

Construct spectra, multiplicities, and measurable eigenvalue events on the actual surfaces. Prove the required estimates for test functions on pairs of pants, min–max, and Cheeger/Buser inequalities.

<details>
<summary>View individual obligations</summary>

<a id="task-hyp-spectral"></a>

- [ ] **[Discrete spectra and local variational estimates on pairs of pants (HYP-SPECTRAL)](CLASSICAL_RESULTS.md#input-hyp-spectral)**

  Construct Laplacian spectrum with multiplicity and measurable eigenvalue events on G, cusp essential threshold1/4, localized pants trial functions, minmax and Cheeger/Buser bounds.

</details>

<a id="foundation-probability"></a>

## Point measures, Poisson processes, and probability limits

Complete the measurable and topological structures on point-measure spaces, existence of Poisson processes, moment and Laplace-functional formulas, count criteria, and continuous-mapping results.

<details>
<summary>View individual obligations</summary>

<a id="task-ppp-integral-moments"></a>

- [ ] **[Integrals and moments of Poisson point processes (PPP-INTEGRAL-MOMENTS)](CLASSICAL_RESULTS.md#input-ppp-integral-moments)**

  Prove Campbell first and second moments from disjoint-window count laws via simple function approximation; use bounded-support Poisson count domination for every finite moment. Vague Borel and count-generated sigma-fields agree on the NNReal Radon space as in existing registered count measurability input.

<a id="task-prob-ae-cmt"></a>

- [ ] **[Convergence in distribution under almost-everywhere continuous maps (PROB-AE-CMT)](CLASSICAL_RESULTS.md#input-prob-ae-cmt)**

  Formalize the generic a.e.-continuous mapping theorem for actual weak convergence, reusing Mathlib probability laws/portmanteau. Handle eventually probabilistic sequences by restriction to a cofinal tail.

<a id="task-prob-factorial-pos"></a>

- [ ] **[A factorial-moment criterion for Poisson limits with positive rates (PROB-FACTORIAL-POS)](CLASSICAL_RESULTS.md#input-prob-factorial-pos)**

  Prove the classical full factorial-moment criterion, moment determination and varying-space/cofinal/a.e. versions. Reuse Mathlib Poisson measures and law convergence.

<a id="task-prob-factorial-zero"></a>

- [ ] **[Extending the factorial-moment criterion to zero rates (PROB-FACTORIAL-ZERO)](CLASSICAL_RESULTS.md#input-prob-factorial-zero)**

  Prove finite zero-coordinate Markov convergence, positive-subvector extraction and continuous reinsertion into full vector. This is a generic probability corollary, no paper-specific result.

<a id="task-prob-first-cmt"></a>

- [ ] **[Convergence in distribution of the selected first point (PROB-FIRST-CMT)](CLASSICAL_RESULTS.md#input-prob-first-cmt)**

  Prove finite-window atom matching at unique first atoms, Borel cutoffs and finite-mark first-selector graph continuity; apply generic CMT and approximation, remove high marks via noescape and high time via finite limiting first state; control arbitrary invalid choices by their outer probability.

<a id="task-prob-pm-laplace-cmt"></a>

- [ ] **[Convergence in distribution of point measures from Laplace functionals (PROB-PM-LAPLACE-CMT)](CLASSICAL_RESULTS.md#input-prob-pm-laplace-cmt)**

  Prove the generic Laplace transform criterion for random locally finite counting measures on NNReal, using transform continuity for all t*f and a genuine vague tightness/uniqueness theorem; discharge this precise explicit Prop without paper-specific hypotheses.

<a id="task-prob-point-borel"></a>

- [ ] **[The measurable structure on point-measure spaces (PROB-POINT-BOREL)](CLASSICAL_RESULTS.md#input-prob-point-borel)**

  Formalize actual vague topology, Radon counting-measure Polish/Borel structure and count generators; extract countable representatives for AEMeasurable source maps. No WP instance or paper limit is imported.

<a id="task-prob-poisson-laplace"></a>

- [ ] **[The Laplace functional of Poisson random measures (PROB-POISSON-LAPLACE)](CLASSICAL_RESULTS.md#input-prob-poisson-laplace)**

  Prove random-integral Borel measurability via simple functions and existing count-evaluation sigma-field, finite-window independent Poisson Laplace identity, bounded/monotone approximation and dominated convergence. Eliminate this sole exact root. No actual WP or cluster convergence is supplied.

<a id="task-prob-ppp-exists"></a>

- [ ] **[Existence of Poisson random point measures (PROB-PPP-EXISTS)](CLASSICAL_RESULTS.md#input-prob-ppp-exists)**

  Formalize general Poisson construction and same underlying genuine vague-Borel pointmeasure law; prove locally finite event simultaneously on compact exhaustion and null-set modification. No geometric instance is supplied.

<a id="task-prob-ppp-first"></a>

- [ ] **[The first arrival of a marked Poisson process (PROB-PPP-FIRST)](CLASSICAL_RESULTS.md#input-prob-ppp-first)**

  Formalize measurable marked-atom enumeration, diffuse-time simplicity, finite-prefix/proper-first facts and generic first-arrival law by PPP void/Mecke; supply the exact explicit interface without importing any WP conclusions.

<a id="task-prob-ppp-restriction"></a>

- [ ] **[Restriction and independence of Poisson processes (PROB-PPP-RESTRICTION)](CLASSICAL_RESULTS.md#input-prob-ppp-restriction)**

  Formalize independence of restrictions of a general Poisson process to disjoint measurable sets and its preservation under the actual coordinate maps, then discharge this exact explicit Prop. No WP conclusions are part of this obligation.

<a id="task-prob-vague-counts"></a>

- [ ] **[Point-process convergence from window-count distributions (PROB-VAGUE-COUNTS)](CLASSICAL_RESULTS.md#input-prob-vague-counts)**

  Prove standard Radon pointmeasure tightness/count criterion, semiring extension and C_c test approximations. Nonproper mark projection, paper planar tail, systole and physical scaling remain local obligations. The independently asserted count-law semiring theorem is a distinct real sorry root, not a local proof of the existing moment theorem; prove its separating-class extension independently.

<a id="task-prob-vague-pairing"></a>

- [ ] **[Measurable compactly supported integrals and the vague topology (PROB-VAGUE-PAIRING)](CLASSICAL_RESULTS.md#input-prob-vague-pairing)**

  Prove bounded compact Borel pairing measurability by simple approximation and vague portmanteau continuity with a common compact cutoff. Replace this explicit Prop; construct no paper estimate or geometry conclusion.

<a id="task-prob-vague-topology"></a>

- [ ] **[The vague topology on point measures and positive rescaling (PROB-VAGUE-TOPOLOGY)](CLASSICAL_RESULTS.md#input-prob-vague-topology)**

  Formalize countable metrization of actual Radon vague topology, hereditary subspace properties, and joint dilation compact-test proof: a_j bounded away from0 gives common compact support, cutoff bounds masses, uniform test convergence controls varying integrals. Actual dilation itself is already proved locally.

</details>

<a id="remaining-background"></a>

## Background topics not yet fully covered

These four background topics cover more than the specific classical premises currently registered. Each needs further work, reusing the local proofs already available.

| Background topic | Available results | Missing scope |
| --- | --- | --- |
| Volume and intersection estimates at fixed cusp count | The fixed-n leading term with an unknown universal constant; the first correction at n=0 | All fixed-order polynomial corrections and absolute intersection-difference estimates in the broader background summary |
| Collars and hyperbolic curve tools | Simplicity and disjointness of short primitive geodesics; local packing, doubling, and axial representations | The full pointwise Margulis decomposition; existence and uniqueness of geodesic representatives for every eligible free homotopy class |
| Complex analysis | Precise implicit-function, Pringsheim, Rouché, and Hadamard premises; local Cauchy and two-constants estimates on slit domains | General formal Lagrange inversion in the broader summary |
| Fourier and lattice tools | Analytic probability generating functions, Fourier tools for nonnegative lattices, harmonic inversion, and uniform local limits | The version for general integer-valued distributions, including negative support |

These gaps concern background scope; they do not reclassify the paper's new results as classical assumptions. Every part needed for the original paper targets must be completed.
If a background summary exceeds what the targets require, check its actual uses and state the narrower scope explicitly. Do not change a paper conclusion to bypass a gap.

## Connect the intended objects and complete the project

- [ ] Realize the intersection, WP geometry, hyperbolic curve, cutting, spectral, and probability structures using one compatible family of mathematical objects. Prove compatibility of lengths, measures, labels, and normalizations across interfaces.
- [ ] Instantiate the theorems in the target table. Prove the correspondence between actual WP volumes and the recursive model, so the main results no longer assume geometric interfaces without constructed instances.
- [ ] Complete every classical proof and eliminate `sorry`, `admit`, and unproved paper-specific assumptions. Recheck the quantifiers, parameter ranges, constant dependencies, and error bounds of every paper target.
- [ ] Pass the full build, type checks, and axiom-dependency checks, also inspecting the premises in theorem parameters.

**The project reaches full formalization only after these classical results, infrastructure, and connections to the intended objects are complete, and the final comparison with the paper and machine checks pass.**
