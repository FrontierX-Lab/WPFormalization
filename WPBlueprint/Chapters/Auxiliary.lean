import WPFormalization.Statements
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Foundational definitions and auxiliary targets" =>

:::definition "def:stable" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "3", anchor := "def:stable", citation := "Definition unnumbered", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition unnumbered — Stable pairs and degree conventions.

Genus and cusp/boundary counts are nonnegative integers with $`2g-2+n>0`. For a degree tuple of length n set $`h=2g-2+n`, $`N=3g-3+n`, $`D=\sum_i d_i`, $`m=N-D`. Negative-degree, wrong-dimension and unstable recursion factors vanish; the stated genus-zero initial derivatives are kept separate.
:::

:::definition "def:wp-volume" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:stable")
%%%
source := { document := "paper-v3", spans := #[{ page := "3", anchor := "def:wp-volume", citation := "Definition unnumbered", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition unnumbered — Geometric Weil--Petersson volume.

For a stable pair and nonnegative labeled boundary lengths, use the orbifold convention $`V_{g,n}(L)=\frac1{(3g-3+n)!}\int_{\mathcal M_{g,n}(L)}\omega_{WP}^{3g-3+n}` and $`V_{g,n}=V_{g,n}(0,\ldots,0)`. A zero-length boundary is a cusp. These are geometric volumes, not definitions by a scalar recurrence.
:::

:::definition "def:intersections" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:stable")
%%%
source := { document := "paper-v3", spans := #[{ page := "19", anchor := "def:intersections", citation := "Definition unnumbered", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition unnumbered — Geometric intersection classes and brackets.

On the Deligne–Mumford compactification, $`\psi_i` is the cotangent class and $`\kappa_1` is the logarithmic Mumford class. For stable (g,n), nonnegative degrees and $`m=3g-3+n-|\mathbf d|\ge0`, define $`[\tau_{d_1}\cdots\tau_{d_n}]_{g,n}=\prod_i(2d_i+1)!!\,4^{|\mathbf d|}(2\pi^2)^m\int_{\overline{\mathcal M}_{g,n}}\kappa_1^m\prod_i\psi_i^{d_i}/m!`. Angle brackets are the unweighted pure psi integrals. The geometric identification $`[\omega_{WP}]=2\pi^2\kappa_1` is an external theorem, not a definition.
:::

:::definition "def:bessel" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "4", anchor := "def:bessel", citation := "Definition unnumbered", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition unnumbered — Genus-zero analytic function and inverse branch.

Define the entire function $`X(y)=\sum_{j\ge0}(-1)^jy^{j+1}/(j!(j+1)!)=\sqrt y J_1(2\sqrt y)` and $`a=X^{\prime}`. Let $`y_0=j_{0,1}^2/4` be its first positive derivative zero, $`x_c=X(y_0)`, and let Y(x) denote the inverse branch taking $`[0,x_c)` to $`[0,y_0)`. Kernel properties establish that this inverse and the stationary root are well defined.
:::

