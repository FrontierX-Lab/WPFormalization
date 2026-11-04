# WPFormalization

A Lean 4 and Mathlib formalization of Li–Wang's [*Uniform large-genus asymptotics of Weil–Petersson volumes*](source/paper.pdf).

This is the stage-one deliverable. All 57 numbered results and the registered new derivations have proofs under the listed classical premises. Some classical proofs, the construction of the intended geometric objects, and their compatibility remain to be completed.

| What to read | Document |
| --- | --- |
| Paper statements and their corresponding Lean declarations | [Target table](docs/TARGETS.md) |
| Classical results used by the project, with precise conditions and references | [Classical results](docs/CLASSICAL_RESULTS.md) |
| Outstanding proofs, infrastructure, and object constructions | [Remaining infrastructure](docs/INFRASTRUCTURE.md) |

The [interactive Blueprint](blueprint/index.html) includes paper statements, Lean declaration previews, search, and a clickable dependency graph.
The site is generated from the current source. Its graph uses the dependencies recorded in Blueprint and the proof status of associated Lean declarations. The generated site is included, so readers do not need to install Lean or rebuild it. From the repository root, run:

```bash
python3 -m http.server 8000 --bind 127.0.0.1 --directory blueprint
```

Then open [http://127.0.0.1:8000/](http://127.0.0.1:8000/). The same files can be served by a static web server.

Full formalization requires proving all listed classical results, completing the infrastructure, and connecting it to one compatible family of actual mathematical objects, followed by a final comparison of every target with the paper and machine verification.

Build with the versions pinned in `lean-toolchain` and `lake-manifest.json`:

```bash
lake exe cache get
lake build
```

Run `./scripts/ci-blueprint.sh` for the full checks; Python 3 and Node.js are also required. After source changes, run `lake exe vbp build` and `python3 scripts/export_blueprint.py` to regenerate the site.

The paper remains copyrighted by its authors; the repository copy is provided for formalization and comparison. The project currently has no declared license.
