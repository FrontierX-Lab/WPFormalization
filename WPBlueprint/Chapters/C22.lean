import WPBlueprint.Chapters.C21
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "appG-critical-proofs" =>

# Proofs for the critical length spectrum

This appendix proves Theorem {bpref "thm:critical-cluster"}[14.6], following the outline in Subsection 14.5. Throughout, $`n/\sqrt g\to c\in(0,\infty)`, and $`P_s`, $`K_s`, $`\mu_c` and $`\nu` are as in {bpref "eq:cluster-intensities"}[14.19].

## Ordinary cuts and cusp allocations

Short multicurves are organized by their cut graphs: the vertices are the components of the complement, labeled by their genera, and the edges are the curves. Lemma {bpref "lem:critical-cuts"}[G.1] bounds the expected number of multicurves with a given cut graph. It shows that, in the limit, only nonseparating curves and boundaries of two-cusp pairs of pants contribute; the later subsections compute these contributions jointly.

Fix a connected cut graph with $`k\ge1` edges and $`Q` vertices; loops and multiple edges are allowed. At vertex $`i` let $`a_i` be the genus and $`p_i\ge1` its degree. Then 

$$`\sum_i a_i=g-k+Q-1,\qquad \sum_i p_i=2k.`

 Partition the vertices into $`u` of type $`(0,1)`, $`v` of type $`(0,2)`, and $`w` with $`h_i=2a_i-2+p_i\ge1`. Put $`h_0=2g-2`. For large $`g`, $`w\ge1`, and the latter complexities sum to $`H=h_0+u`. A component of type $`(0,1)` needs at least two cusps, and one of type $`(0,2)` at least one.

:::lemma_ "lem:critical-cuts" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-Phi")
%%%
source := { document := "paper-v3", spans := #[{ page := "104", anchor := "lem:critical-cuts", citation := "Lemma G.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma G.1 — Critical cut estimate.

Fix $`k` and a bound on the cut lengths. At $`n/\sqrt g\to c>0`, the expected number of cut multicurves of the specified graph and vertex partition, summed over all admissible genera and cusp allocations, is $`O(g^{1-w-v/2})`. If a specified $`(0,1)` component has at least three cusps, the bound gains a factor $`g^{-1/2}`.
:::



:::proof "lem:critical-cuts" (uses := "ext:shen-wu-volumes, ext:mir-integration")
Write $`h_n=2g-2+n` for the complexity of the cusped surface. The volume bounds in \[79\] Lemmas 18–19 give 

$$`V_{a,b}\le C\frac{(4\pi^2)^{d-1}\Gamma(d)}{\sqrt d},
 \quad d=2a-2+b\ge1,\qquad
 V_{g,n}\ge c_0\frac{(4\pi^2)^{h_n-1}\Gamma(h_n)}{\sqrt{h_n}}.`

 The first bound includes $`d=1` after enlarging $`C` for $`(0,3)` and $`(1,1)`; the second uses $`n=O(\sqrt g)`. If vertex $`i` receives $`q_i` cusps, put $`d_i=h_i+q_i`. Then $`\sum_i d_i=h_n` and $`\sqrt{h_n}/\prod_i\sqrt{d_i}\le\sqrt Q`. Mirzakhani integration, the bounded-boundary estimate \[64\] Lemma 3.2, and the multinomial allocation of cusp labels therefore bound the expected cut count $`E_{g,n}` by 

$$`E_{g,n}\le\frac{C_{k,c}\,n!}{\Gamma(h_n)}
       \sum_{\substack{\text{admissible genera}\\q_1+\cdots+q_Q=n}}
       \prod_i\frac{\Gamma(h_i+q_i)}{q_i!}.`

 Here and below the constants may also depend on the length bound. The powers of $`4\pi^2` leave only the fixed factor $`(4\pi^2)^{1-Q}`.

The cusp sums at the two unstable vertex types are bounded using 

$$`\phi_{0,1}(z)=\sum_{q\ge2}\frac{z^q}{q(q-1)}=\frac{z^2}{2}+O(z^3),
 \qquad \phi_{0,2}(z)=\sum_{q\ge1}\frac{z^q}{q}=z+O(z^2).`

 At a stable vertex their generating function is $`\Gamma(h)(1-z)^{-h}`. Moreover 

$$`\sum_{\substack{h_1+\cdots+h_w=H\\h_i\ge1}}
       \prod_i\Gamma(h_i)\le C_w\Gamma(H-w+1).`

 For $`w=2` this follows by dividing by $`\Gamma(H-1)` and summing $`\binom{H-2}{h_1-1}^{-1}`; iteration gives the general bound. Dropping genus parity constraints only increases the sum. Let $`a_m=[z^m]\phi_{0,1}(z)^u\phi_{0,2}(z)^v`. Expanding $`(1-z)^{-H}` gives 

$$`E_{g,n}\le C_{k,c}\frac{\Gamma(H-w+1)}{\Gamma(H)}
       \sum_{m\le n}a_m(n)_m\frac{\Gamma(h_n+u-m)}{\Gamma(h_n)}.`

 Uniformly for $`m\le n=O(\sqrt{h_n})`, the finite-product formula for the Gamma ratio gives $`\Gamma(h_n+u-m)/\Gamma(h_n)\le C_{k,c}h_n^{u-m}`: the logarithmic error is $`O((m+1)^2/h_n)`. Since $`(n)_m\le n^m`, positivity yields 

$$`E_{g,n}\le C_{k,c}h_n^{u-w+1}\phi_{0,1}(n/h_n)^u\phi_{0,2}(n/h_n)^v
          =O(g^{1-w-v/2}).`

 Requiring three cusps at a specified $`(0,1)` vertex replaces one $`\phi_{0,1}(z)` by $`\phi_{0,1}(z)-z^2/2` and gains $`n/h_n=O(g^{-1/2})`.
:::



Only $`w=1`, $`v=0` can survive: the graph then has one large-genus vertex, loops at that vertex, and two-cusp pants attached as leaves. All other graphs, and all leaves with more than two cusps, vanish.

## Excluding complex short subsurfaces

We need expectation bounds, not only a bound on the probability of a bad configuration, so we give the multiplicity argument explicitly.

:::lemma_ "lem:primitive-count" (parent := "paper_core") (tags := "paper-new") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "105", anchor := "lem:primitive-count", citation := "Lemma G.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma G.2 — Bounded primitive count.

For fixed $`K,L`, a finite-area hyperbolic surface $`S` with geodesic boundary and $`0<-\chi(S)\le K` has at most $`C(K,L)` primitive unoriented geodesics of length at most $`L`, uniformly in its metric.
:::



:::proof "lem:primitive-count" (uses := "ext:collar")
Double $`S` along its boundaries. The double has area at most $`4\pi K`. Fix a Margulis constant $`\varepsilon>0`. A primitive geodesic wholly in a thin component is its core; there are boundedly many such cores. Every other geodesic meets the thick part. A maximal $`\varepsilon/4`-separated net there has bounded cardinality by area packing. At each net point, orbit points of a lift are uniformly separated, so hyperbolic ball packing bounds the number of based loops of length at most $`L+\varepsilon`. Connecting a short geodesic to a net point proves the assertion. Primitivity is preserved upon inclusion in the double or in an ambient surface: a root would have the same geodesic image and would already be a closed curve in $`S`.
:::



:::lemma_ "lem:critical-complex" (parent := "paper_core") (tags := "paper-new") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "105", anchor := "lem:critical-complex", citation := "Lemma G.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma G.3 — Complex short configurations.

Fix $`r` and $`L`. As $`g\to\infty` with $`n/\sqrt g\to c\in(0,\infty)`, 

$$`\mathbb E[\text{intersecting ordered simple $r$-tuples of lengths
 at most $L$}]=O_{r,L,c}(g^{-1/2}),`

 

$$`\mathbb E[\text{nonsimple primitive curves of length at most $L$
 not filling two-cusp pants}]=O_{L,c}(g^{-1/2}),`

 and the expected number of simple separating curves of length at most $`L` that are not waists of two-cusp pairs of pants tends to zero.
:::



:::proof "lem:critical-complex" (uses := "lem:critical-cuts, lem:primitive-count, ext:short-filling")
For fixed $`r,L`, a tuple of $`r` distinct simple geodesics of length at most $`L` has bounded total intersection number. We use the local segment argument in the proof of \[65\] Proposition 4.5; it applies equally in the presence of cusps. Thicken each nonannular component of their union, fill complementary disks and peripheral once-punctured disks, and tighten the essential boundaries. The resulting pieces have bounded topology and total boundary length at most $`2rL`. Keep one ambient geodesic for each parallel boundary class. Empty annuli between parallel copies collapse; their two incidences are the two sides of a single edge, possibly a loop. An annulus with cusps does not collapse and is a $`(0,2)` component counted among the $`v` vertices. Isolated tuple curves are retained as additional cut edges, unless they are already one of the tightened boundaries. Minimal intersection ensures that these boundaries are disjoint from the original tuple.

There are finitely many resulting graph shapes and markings at fixed $`r,L`. For a fixed cut multicurve, Lemma {bpref "lem:primitive-count"}[G.2] bounds the choices of original curves in each marked piece. Hence the tuple count is bounded pointwise by a constant times a finite sum of marked cut-multicurve counts. An intersecting simple tuple cannot fill two-cusp pants. Its marked component either has $`h_i\ge1`, forcing a second stable vertex to carry the unbounded genus, or has type $`(0,2)`, or has type $`(0,1)` with at least three cusps. The bounds in Lemma {bpref "lem:critical-cuts"}[G.1] give G.3.

For a single nonsimple primitive curve of length at most $`L`, use the filling construction of \[37\] Definition 4.10 and Lemma 4.11. The filled piece has boundary length at most $`2L` and area at most $`4L`, so its topology is bounded. The same recording retains formal boundary sides that tighten to the same ambient curve as sides of a cut edge. Lemma {bpref "lem:primitive-count"}[G.2] controls the number of curves filling each piece. The preceding classification therefore gives G.4. A filled piece cannot be the whole ambient surface for large $`g`, since its topology is bounded. Finally, the one-edge case of Lemma {bpref "lem:critical-cuts"}[G.1] shows that simple separating curves of bounded length other than two-cusp pants waists vanish in expectation.
:::



## Joint nonseparating and pants counts

Let $`\mathcal N_g` count simple nonseparating lengths and let $`\mathcal Q_g` count two-cusp pants waist lengths.

:::lemma_ "lem:critical-skeleton" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:SP3")
%%%
source := { document := "paper-v3", spans := #[{ page := "106", anchor := "lem:critical-skeleton", citation := "Lemma G.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma G.4 — Joint Poisson limit.

As $`g\to\infty` with $`n/\sqrt g\to c\in(0,\infty)`, 

$$`(\mathcal N_g,\mathcal Q_g)\Longrightarrow
 (\mathcal N,\mathcal Q_c)`

 jointly in the vague topology on $`[0,\infty)`, where $`\mathcal N` and $`\mathcal Q_c` are independent Poisson point processes of intensities $`\nu` and $`\mu_c`.
:::



:::proof "lem:critical-skeleton" (uses := "lem:critical-cuts, lem:critical-complex, thm:volume, prop:bounded-boundaries, ext:mir-integration")
In the mixed factorial moments of $`(\mathcal N_g,\mathcal Q_g)`, G.3 removes intersecting tuples. Lemma {bpref "lem:critical-cuts"}[G.1] removes every disjoint cut type except the graph with a single large component, $`k` nonseparating loops and $`r` two-cusp leaves. For prescribed bounded intervals for the $`k+r` lengths, its exact contribution is 

$$`\frac{(n)_{2r}}{2^{r+k}V_{g,n}}
 \int V_{g-k,n-r+2k}(\mathbf s,\mathbf t,\mathbf t,0^{n-2r})
        \prod_{j=1}^r s_j\,\mathrm ds_j
        \prod_{i=1}^k t_i\,\mathrm dt_i.`

 Here $`(n)_{2r}` is the falling factorial. The factor $`2^{-r}` counts unordered pairs of cusp labels at the ordered pants leaves, as in \[79\] Lemma 28; $`2^{-k}` exchanges the sides of each nonseparating cut, as in \[65\] Proposition 4.2. There is no factor $`r!` or $`k!`, since both tuples are ordered.

The volume ratio is a product of $`r` cusp ratios and $`k` genus ratios. The cusp ratios satisfy $`V_{g,j+1}/V_{g,j}\sim8\pi^2g` for $`j\le n` by \[66\] Lemma 5.1(ii), since $`n=o(g)`. For the genus ratios, \[66\] Lemma 5.1(iii) gives only an upper bound, and the two-sided limit at $`n\asymp\sqrt g` is the zero-density case $`\mathcal B(0)=1` of Theorem {bpref "thm:volume"}[1.3]. Together, 

$$`\frac{V_{g-k,n-r+2k}}{V_{g,n}}\sim(8\pi^2g)^{-r}.`

 Proposition {bpref "prop:bounded-boundaries"}[9.4], applied at zero limiting density, where $`\mathfrak b_0(L)=\sinh(L/2)/(L/2)`, supplies, uniformly on the fixed length box, the boundary factor $`\prod_j S(s_j/2)\prod_i S(t_i/2)^2`, with $`S(t)=\sinh(t)/t`; compare Shen–Wu’s bounded-boundary estimate \[79\] Proposition 25, which they attribute essentially to \[65\] Proposition 3.1 and \[70\] Lemma 20. Consequently the limiting factors in G.6 are 

$$`\frac12 tS(t/2)^2\,\mathrm dt=\nu(\mathrm dt),\qquad
 \frac{c^2}{16\pi^2}sS(s/2)\,\mathrm ds=\mu_c(\mathrm ds).`

 All mixed factorial moments on disjoint bounded intervals converge to those of independent Poisson counts. Higher fixed moments give uniform integrability, and the multivariate Poisson law is moment determinate. The first-moment bounds near zero are $`O(\varepsilon^2)`. This proves the lemma.
:::



## Proof of Theorem {bpref "thm:critical-cluster"}[14.6]

:::proof "thm:critical-cluster" (uses := "lem:critical-skeleton, lem:critical-complex, lem:primitive-count")
Fix $`L<\infty`. By Lemma {bpref "lem:critical-complex"}[G.3], with probability tending to one every nonsimple primitive curve of length at most $`L` fills two-cusp pants with waist at most $`2L`. By G.3, the pants waists up to $`2L` are pairwise disjoint with probability tending to one. The pants interiors are then disjoint as well. Other simple separating curves up to $`L` are absent with probability tending to one. On this event, the full primitive counting measure restricted to $`[0,L]` is exactly 

$$`\left.\left(\mathcal N_g+
       \sum_{s\in\mathcal Q_g\cap[0,2L]}K_s\right)\right|_{[0,L]}.`

 Every interior primitive geodesic of $`P_s` is nonsimple and fills it. The filling boundary bound implies $`s\le2\ell` for such a geodesic of length $`\ell`. Thus pants with waist greater than $`2L` cannot contribute, and the limiting sum is locally finite.

For $`\varepsilon>0`, the family $`P_s`, $`\varepsilon\le s\le2L`, is compact in its fixed-topology moduli space. Lengths of marked classes vary continuously, and only finitely many such classes have length at most $`L` somewhere on this compact family. For the latter assertion, use a finite cover by uniformly bilipschitz markings, with standard neighborhoods at the two cusps, and the finiteness of each center metric’s length spectrum below a fixed bound. Hence $`s\mapsto\langle f,K_s\rangle` is continuous away from zero for continuous compactly supported $`f`. Apply G.5 with waist cutoff $`\varepsilon`, choosing $`L` larger than the support of $`f`. The probability of removing any waist is at most $`\mathbb E\mathcal Q_g([0,\varepsilon])`, whose limit is $`\mu_c([0,\varepsilon])=O(\varepsilon^2)`. Letting $`\varepsilon\downarrow0` proves 14.20. The independent Poisson Laplace functionals give 14.21.
:::


