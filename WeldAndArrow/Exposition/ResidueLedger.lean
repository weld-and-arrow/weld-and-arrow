import WeldAndArrow.Exposition.Basic

namespace WAA.Exposition

structure ResidueEntry where
  id : String
  locus : DocId
  reason : String
  anchors : List Lean.Name := []
deriving Repr

def residueLedger : List ResidueEntry := [
  { id := "glossary-accuracy"
    locus := "glossary"
    reason := "Gloss accuracy and canonical caveats remain prose obligations." },
  { id := "designation-universe-adequacy"
    locus := "identification"
    reason := "Adequacy of the modeled designation-universe to the avyākata questions remains a modeling claim." },
  { id := "an663-correlation"
    locus := "theorems"
    reason := "The AN 6.63 correlation, peaks reading, and comparative claim against event-typed theories remain prose-bound." },
  { id := "hakuin-epigram"
    locus := "theory"
    reason := "The Hakuin epigram pedigree is mixed and load-free for the checked mechanism." },
  { id := "kuoan-locus"
    locus := "theorems"
    reason := "The exact Kuòān verse locus for the Ten Bulls guard should be verified across translations." },
  { id := "historical-contra-dogen"
    locus := "theory"
    reason := "The Daishugyō/Jinshin inga historical contra is owned as interpretation, not discharged by Lean." }
]

example : residueLedger.length = 6 := rfl

end WAA.Exposition
