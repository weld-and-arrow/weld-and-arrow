import WeldAndArrow.Signature
import WeldAndArrow.Consequences
import WeldAndArrow.Doctrines
import WeldAndArrow.Identification
import WeldAndArrow.Meta
import WeldAndArrow.Exposition

/-!
Root module for the `WeldAndArrow` library.

Layers:
* `Signature`: definitions and primitive interfaces.
* `Consequences`: neutral lemma library, including the error taxonomy.
* `Doctrines`: discourse-facing checked conditionals with sibling negatives.
* `Identification`: the naming claim, ownership vocabulary, placements,
  disclaimers, commentary, and placement-gating results.
* `Meta`: invariance discipline, sibling countermodels, verdict ledger, and
  audit.
* `Exposition`: generated prose data, rendering, and prose-surface checks.

Placement rules:
1. Place a declaration by the vocabulary its statement consumes.
2. Put negative witnesses in the sibling module of the claim they gate.
3. Preserve the layer DAG: Signature -> Consequences -> Doctrines ->
   Identification -> Meta -> Exposition.
4. Explanatory content that exists only to read the code lives in
   `Exposition`; no grid layer imports `Exposition`; `Exposition` defines no
   grid vocabulary and proves nothing about the grid.
-/
