/-
================================================================================
  WeldAndArrow.FourTruths
  Checked four-truth-facing consequences in the grid's own vocabulary
================================================================================

This module names the dukkha-facing mismatch grade without adding a new
measure. Mismatch covaries with share because it is read from the same Row-2
display value; the grid proves the implication-shape facts and does not assert
any detached injunction.
-/

import WeldAndArrow.Theorems

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- ==============================================================================
   Truths 1-3: mismatch as a display reading
============================================================================== -/

/-- Mismatch's grade is read from the same structure as share. This is
    covariation, not a second operational measure. -/
def MismatchGrade (w : G.Weld) : Contrib :=
  G.share w

@[simp]
theorem mismatchGrade_eq_share (w : G.Weld) :
    G.MismatchGrade w = G.share w :=
  rfl

/-- Ordinal covariation: lowering share lowers mismatch grade in the same
    display order, because the two readings unfold to the same value. -/
theorem mismatchGrade_le_of_share_le {w₁ w₂ : G.Weld}
    (h : G.share w₁ ≼ G.share w₂) :
    G.MismatchGrade w₁ ≼ G.MismatchGrade w₂ :=
  h

/-- Live mismatch is an actual occurrence with a live self-pole index. -/
def MismatchLive (w : G.Weld) : Prop :=
  G.Actual w ∧ G.HasSelfPoleIndex w

/-- Given occurrence actuality, live mismatch is exactly the live self-pole
    index condition. -/
theorem mismatchLive_iff_hasSelfPoleIndex
    {w : G.Weld} (hactual : G.Actual w) :
    G.MismatchLive w ↔ G.HasSelfPoleIndex w := by
  constructor
  · intro h
    exact h.right
  · intro hidx
    exact ⟨hactual, hidx⟩

/-- Stones are outside the actual occurrence-domain for live mismatch. -/
theorem not_mismatchLive_of_stone
    (b : G.Being) (hstone : G.Stone b) {c : G.Call} {r : G.Response} :
    ¬ G.MismatchLive ⟨b, c, r⟩ := by
  intro h
  exact G.not_actual_of_stone b hstone h.left

/-- A terminus response has mismatch grade at the pole-class. -/
theorem mismatch_atBot_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    AtBot (G.MismatchGrade ⟨b, c, r⟩) :=
  G.atBot_of_terminus_response hterm hresp

/-- A terminus response is not live mismatch. -/
theorem not_mismatchLive_of_terminus_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    ¬ G.MismatchLive ⟨b, c, r⟩ := by
  intro h
  exact h.right (G.mismatch_atBot_of_terminus_response hterm hresp)

end Grid

end WAA
