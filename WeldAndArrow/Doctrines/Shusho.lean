/-
================================================================================
  WeldAndArrow.Doctrines.Shusho
  Per-occurrence full-enlightenment face and standing-display fence
================================================================================

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import WeldAndArrow.Doctrines.Sraddha

namespace WAA

namespace Grid

namespace DirectedConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/-- The sho face of a single occurrence: an actual weld whose share sits in
    the pole-class. No standing rank is implied; the fact is about this act
    and is spent with it. Reading and motivation: Identification/Commentary.lean,
    C.4. -/
def WaaPoleDeed (w : G.Weld) : Prop :=
  G.Actual w ∧ AtBot (G.share w)

/-- Shusho-itto, grid-side: full enlightenment as a fact about one delivered
    occurrence -- a pole-typed actual deed landing with a share-drop against a
    live prior tendency. This, not the standing predicate, is what act-time
    verdicts may assert. Reading and motivation: Identification/Commentary.lean,
    C.4. -/
def WaaEnlightenedOccurrence
    (before : Config Contrib) (deed reception : G.Weld) : Prop :=
  WaaPoleDeed G deed ∧
    ¬ AtBot before.tendency ∧
      LandsWithShareDrop G before deed reception

theorem waaEnlightenedOccurrence_hasShareDropLanding
    {before : Config Contrib} {deed reception : G.Weld}
    (h : WaaEnlightenedOccurrence G before deed reception) :
    HasShareDropLanding G before deed :=
  ⟨reception, h.right.right⟩

theorem waaPoleDeed_of_terminus_response
    {w : G.Weld} (hterm : G.Terminus w.agent) (hactual : G.Actual w) :
    WaaPoleDeed G w :=
  ⟨hactual, G.atBot_of_terminus_response hterm hactual⟩

/-- The standing display entails an occurrence face only once the deed is an
    actual mounted response and the regime supplies a live delivered pair. The
    landing witness may be a different actual reception from the supplied
    delivery, because `ShortfallClosedAt` asserts existence of a share-drop
    landing for that deed. -/
theorem waaEnlightenedOccurrence_of_waaFullyEnlightened
    {b : G.Being} {before : Config Contrib} {deed reception : G.Weld}
    (h : WaaFullyEnlightened G b)
    (hdeed : deed.agent = b)
    (hactual : G.Actual deed)
    (hdel : DeliveredTo G deed reception)
    (hlive : ¬ AtBot before.tendency) :
    ∃ reception',
      WaaEnlightenedOccurrence G before deed reception' := by
  rcases shortfallClosedAt_of_waaFullyEnlightened G h hdeed hlive hdel with
    ⟨reception', hland⟩
  refine ⟨reception', ?_⟩
  refine ⟨?_, hlive, hland⟩
  have htermDeed : G.Terminus deed.agent := by
    simpa [hdeed] using h.left.right
  exact waaPoleDeed_of_terminus_response G htermDeed hactual

/-- The old sraddha landing route factors through the per-occurrence face once
    the speaker's deed is known to be actual. -/
theorem waa_path_landing_factors
    {g : G.Being} {before : Config Contrib} {deed reception : G.Weld}
    (hfaith : WaaFullyEnlightened G g)
    (hdeed : deed.agent = g)
    (hactual : G.Actual deed)
    (hdel : DeliveredTo G deed reception)
    (hctx : WaaAversionContext G before reception) :
    ∃ reception',
      WaaEnlightenedOccurrence G before deed reception' :=
  waaEnlightenedOccurrence_of_waaFullyEnlightened
    G hfaith hdeed hactual hdel hctx.liveBefore

/-- Earned, non-vacuous full-enlightenment display: the standing pattern plus
    at least one actual enlightened occurrence witnessing it. The sealed-regime
    terminus satisfies the standing predicate vacuously and fails this enacted
    form. -/
def WaaEnlightenmentEnacted (b : G.Being) : Prop :=
  WaaFullyEnlightened G b ∧
    ∃ before deed reception,
      deed.agent = b ∧ WaaEnlightenedOccurrence G before deed reception

theorem waaFullyEnlightened_of_enacted
    {b : G.Being} (h : WaaEnlightenmentEnacted G b) :
    WaaFullyEnlightened G b :=
  h.left

theorem not_enacted_of_undelivered
    {b : G.Being}
    (hundelivered : ∀ (deed reception : G.Weld),
      deed.agent = b → ¬ DeliveredTo G deed reception) :
    ¬ WaaEnlightenmentEnacted G b := by
  rintro ⟨_hstanding, before, deed, reception, hdeed, hocc⟩
  exact hundelivered deed reception hdeed
    (deliveredTo_of_landsWithShareDrop G hocc.right.right)

namespace BeingConvention
namespace GridConvention

/-- Per-occurrence enlightened landing is a grammatical verdict item. -/
def WaaEnlightenedOccurrenceVoice : ErrorGrade :=
  ErrorGrade.verdict

/-- The standing universal is displayable as shortfall-voiced, not assertable
    as an act-time verdict. -/
def WaaStandingEnlightenmentVoice : ErrorGrade :=
  ErrorGrade.shortfall

theorem waa_enlightened_occurrence_voice_assertable :
    ErrorGrade.voice WaaEnlightenedOccurrenceVoice = VerdictVoice.assertable :=
  rfl

theorem waa_standing_enlightenment_voice_displayable :
    ErrorGrade.voice WaaStandingEnlightenmentVoice = VerdictVoice.displayable :=
  rfl

end GridConvention
end BeingConvention

end DirectedConvention

end Grid

end WAA
