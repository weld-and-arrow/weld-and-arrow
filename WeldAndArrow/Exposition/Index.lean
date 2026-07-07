import WeldAndArrow.Exposition.Basic

namespace WAA.Exposition

def indexBody : String := r#"
## Contents

0. **Contents** — this table of contents.
1. **Theory** — the motivations and the rules: the floor, the act-grammar, the grade and its determination, the domain joint and orthogonality, the karma circuit and its three registers, the weld's two faces, the separate/fuse rule; one act run whole through the grid; [Glossary.md](Glossary.md).
2. **Theorems** — what falls out of the rules directly (backsliding, memory and prudence, dukkha, the transposition, the error-taxonomy) and the derivations that meet existing discourses (MMK 17, the three killings and AN 6.63, sudden and gradual, other-power, pariṇāmanā, transcription, the Ten Bulls, Five Ranks, and stage-schemes); with the instructive absences in both.
3. **The Identification and Placements** — the karma identification, the offices-spine that earns the name, the sower/reaper split, the contemporary placements, the pole-typing corollary, the taxonomy's internal mis-feeds, and the disclaimers, enumerated.
4. **Formalization** — a reading of the Lean formalization.
5. **Glossary** — a generated glossary.
"#

def indexDoc : Doc :=
  { id := "index"
    title := "Contents"
    output := "Exposition/index.md"
    source := "WeldAndArrow/Exposition/Index.lean"
    summary := "Contents page for the generated exposition."
    blocks := [.raw indexBody] }

end WAA.Exposition