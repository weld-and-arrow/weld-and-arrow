import WeldAndArrow.Exposition.Basic
import WeldAndArrow.Meta.Glossary

namespace WAA

def renderSeeAlso (refs : List String) : String :=
  match refs with
  | [] => "—"
  | names =>
      Exposition.joinComma
        (names.map (fun name => "`" ++ Exposition.markdownEscape name ++ "`"))

def renderGlossaryRow (entry : GlossaryEntry) : String :=
  "| " ++ Exposition.markdownEscape entry.term ++
  " | " ++ Exposition.markdownEscape entry.kind.label ++
  " | " ++ Exposition.markdownEscape entry.gloss ++
  " | " ++ Exposition.renderAnchors entry.anchors ++
  " | " ++ renderSeeAlso entry.seeAlso ++
  " |"

def glossaryBody : String :=
  "# Glossary\n\n" ++
  "Generated from `WeldAndArrow/Meta/Glossary.lean` and " ++
  "`WeldAndArrow/Exposition/Glossary.lean` by `lake exe exposition_gen`. " ++
  "Gloss accuracy remains prose; Lean checks term uniqueness, backward `seeAlso` references, and anchor resolvability. " ++
  "Canonical Buddhist terms are glossed for newcomers; expert caveats live in the Disclaimers.\n\n" ++
  "| Term | Kind | Definition | Checked anchors | See also |\n" ++
  "| --- | --- | --- | --- | --- |\n" ++
  String.intercalate "\n" (glossary.map renderGlossaryRow) ++ "\n"

def glossaryDoc : Exposition.Doc :=
  { id := "glossary"
    title := "Glossary"
    output := "Exposition/Glossary.md"
    source := "WeldAndArrow/Exposition/Glossary.lean"
    summary := "A generated glossary."
    blocks := [.raw glossaryBody] }

def renderGlossary : String :=
  Exposition.renderDoc glossaryDoc

end WAA
