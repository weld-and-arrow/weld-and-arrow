import WeldAndArrow.Exposition.Docs

namespace WAA.Exposition

def renderedDocs : List (String × String) :=
  allDocs.map (fun doc => (doc.output, renderDoc doc))

def writeDocs : IO Unit := do
  for (path, content) in renderedDocs do
    IO.FS.writeFile path content

def checkDocs : IO Unit := do
  let mut mismatches : Array String := #[]
  for (path, expected) in renderedDocs do
    let current <- IO.FS.readFile path
    if current != expected then
      mismatches := mismatches.push path
  unless mismatches.isEmpty do
    let details := mismatches.foldl (fun acc path => acc ++ "\n" ++ path) ""
    throw (IO.userError s!"exposition output drift:{details}")

end WAA.Exposition

def main (args : List String) : IO Unit := do
  if args.contains "--check" then
    WAA.Exposition.checkDocs
  else
    WAA.Exposition.writeDocs
