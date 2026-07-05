import WeldAndArrow.Signature
import WeldAndArrow.Consequences
import WeldAndArrow.Doctrines
import WeldAndArrow.Identification
import WeldAndArrow.Meta

/-!
Root module for the `WeldAndArrow` library.

Layers:
* `Signature`: definitions and primitive interfaces.
* `Consequences`: neutral lemma library, including the error taxonomy.
* `Doctrines`: discourse-facing checked conditionals with their gating negatives.
* `Identification`: the naming claim, ownership vocabulary, placements,
  disclaimers, commentary, and placement-gating results.
* `Meta`: invariance discipline, vocabulary-discipline countermodels, and audit.

Placement rules:
1. Place a declaration by the vocabulary its statement consumes.
2. Put negative witnesses next to the claim they gate.
3. Preserve the layer DAG: Signature -> Consequences -> Doctrines ->
   Identification -> Meta.
-/
