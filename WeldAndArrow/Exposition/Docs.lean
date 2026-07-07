import WeldAndArrow.Exposition.Glossary
import WeldAndArrow.Exposition.Index
import WeldAndArrow.Exposition.Theory
import WeldAndArrow.Exposition.Theorems
import WeldAndArrow.Exposition.Identification
import WeldAndArrow.Exposition.Formalization.Reading
import WeldAndArrow.Exposition.Thesis

namespace WAA.Exposition

def allDocs : List Doc := [
  indexDoc,
  theoryDoc,
  theoremsDoc,
  identificationDoc,
  formalizationDoc,
  WAA.glossaryDoc
]

example : allDocs.length = 6 := rfl

end WAA.Exposition
