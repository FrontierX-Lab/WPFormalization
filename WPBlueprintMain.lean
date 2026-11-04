import VersoManual
import VersoBlueprint.PreviewManifest
import WPBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 := do
  let result ← Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc WPBlueprint.Blueprint) args
    (extensionImpls := by exact extension_impls%)
  if result == 0 then
    let output : System.FilePath := ((args.dropWhile (· != "--output")).drop 1).headD "_out/site"
    for mode in ["html-multi", "html-single"] do
      let dir := output / mode / "source"
      IO.FS.createDirAll dir
      IO.FS.writeBinFile (dir / "paper.pdf") (← IO.FS.readBinFile "source/paper.pdf")
  return result
