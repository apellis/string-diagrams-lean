import StringDiagrams.Examples.RenderDemo

/-!
Write the SVG and TikZ drawings of `StringDiagrams.Examples.RenderDemo.gallery` to the
directory `out/` (ignored by Git). Run from the package root, after `lake build`:

```sh
lake env lean --run scripts/render_examples.lean
```
-/

open StringDiagrams.Examples.RenderDemo

def main : IO Unit := do
  IO.FS.createDirAll "out"
  for (name, svg, tikz) in gallery do
    match svg, tikz with
    | .ok svg, .ok tikz =>
      IO.FS.writeFile s!"out/{name}.svg" svg
      IO.FS.writeFile s!"out/{name}.tex" tikz
      IO.println s!"wrote out/{name}.svg and out/{name}.tex"
    | .error e, _ | _, .error e => IO.eprintln s!"{name}: {e}"
