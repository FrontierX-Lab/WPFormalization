import WPBlueprint.Chapters.C22
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Proof dependency map" =>

:::proof "thm:coefficient" (uses := "thm:quantitative-coefficient")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "lem:kernel-zeros" (uses := "ext:complex-analysis")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "lem:kernel-positivity" (uses := "lem:kernel-zeros, ext:complex-analysis")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "lem:parameter" (uses := "lem:kernel-zeros, ext:complex-analysis")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "prop:marked-ratios" (uses := "eq:TL24, eq:TL27, lem:parameter")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:P10" (uses := "lem:kernel-zeros")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:P11" (uses := "lem:kernel-zeros, eq:P10, ext:complex-analysis")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:P13" (uses := "eq:P10, ext:fourier")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:H5" (uses := "ext:mixed-transform")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:H8" (uses := "ext:mixed-transform, ext:dvv")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:H9" (uses := "eq:H6, ext:dvv")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:H10" (uses := "ext:dvv")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:H13" (uses := "eq:P2")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:H14" (uses := "eq:H13")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:H22" (uses := "eq:P13, eq:H13")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:TL12" (uses := "ext:dvv")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:TL14" (uses := "ext:kdv")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:TL19" (uses := "prop:harmonic, lem:monotone, eq:TL12, eq:TL14")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:TL23" (uses := "eq:TL19, lem:monotone")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:TL24" (uses := "eq:TL23, eq:TL12")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:TL27" (uses := "eq:TL24, eq:TL14, eq:TL19")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:PF8" (uses := "lem:first-degree, eq:TL12")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:PF12" (uses := "ext:dvv, ext:iz, ext:painleve-leading")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:PF13" (uses := "ext:dvv")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:AV6" (uses := "eq:TL12")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:C7" (uses := "ext:nef-teissier")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:C8" (uses := "ext:fixed-cusps")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:C18" (uses := "ext:dvv, ext:one-point, ext:mixed-transform")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:C23" (uses := "prop:harmonic, ext:fixed-cusps")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:PS3" (uses := "ext:mir-integration, ext:collar")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:FE14" (uses := "ext:iz, ext:painleve-contour, ext:painleve-borel, ext:stirling")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:CG12" (uses := "thm:canonical-expansion")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

:::proof "eq:CG13" (uses := "eq:CG12")
The complete informal argument is transcribed in the corresponding chapters, including the supporting appendices. The proof dependencies recorded here are the specific inputs to that argument; this outline carries no Lean proof status.
:::

