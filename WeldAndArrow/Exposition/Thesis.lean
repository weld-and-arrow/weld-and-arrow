import WeldAndArrow.Exposition.Basic
import WeldAndArrow.Signature
import WeldAndArrow.Identification.Ownership

namespace WAA.Exposition

structure ThesisClause where
  id : String
  text : String
  status : ClaimStatus
  anchors : List Lean.Name := []
deriving Repr

def thesisClauses : List ThesisClause := [
  { id := "diachronicToField"
    text := "Everything diachronic belongs to the field"
    status := .checked
    anchors := [``Config] },
  { id := "indexEnactedNotStored"
    text := "every index is enacted and nothing indexed is stored"
    status := .checked
    anchors := [``Grid.index, ``Grid.rePitch_forgets] },
  { id := "karmaNamesLoop"
    text := "karma names this loop"
    status := .checked
    anchors := [``Grid.DirectedConvention.WaaOwnershipFace] },
  { id := "namingEarnedByFit"
    text := "and the naming is earned by fit"
    status := .proseBound "fit to the traditional offices is argued in exposition"
    anchors := [``Grid.DirectedConvention.WaaReportFace,
      ``Grid.DirectedConvention.WaaOwnershipFace] }
]

def thesisSentence : String :=
  "Everything diachronic belongs to the field; every index is enacted and nothing indexed is stored; karma names this loop, and the naming is earned by fit"

def thesisRender : String :=
  "**" ++ thesisSentence ++ "** — the tradition's uses of karmic ownership (cetanā, reception, remorse, absolution, dedication) discharge natively at act-time."

example : thesisSentence =
    "Everything diachronic belongs to the field; every index is enacted and nothing indexed is stored; karma names this loop, and the naming is earned by fit" := rfl

end WAA.Exposition
