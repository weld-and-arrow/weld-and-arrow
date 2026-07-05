/-
================================================================================
  WeldAndArrow.Theorems
  Checked consequences of WeldAndArrow.Theory
================================================================================

This module proves consequences of the primitive definitions: order facts,
function/share facts, re-pitch facts, delivery and landing projections, pair
projections, and tier diagnostics.

Reading and motivation: Identification.lean, Commentary C.2.
-/

import WeldAndArrow.Theory

namespace WAA

section Preorder

variable {α : Type} [Preorder α]

/-- Incomparability is symmetric. -/
theorem incomparable_symm {a b : α} (h : Incomparable a b) :
    Incomparable b a :=
  ⟨h.right, h.left⟩

/-- Incomparability rules out the left-to-right comparison. -/
theorem not_le_of_incomparable {a b : α} (h : Incomparable a b) :
    ¬ a ≼ b :=
  h.left

/-- Incomparability rules out the right-to-left comparison. -/
theorem not_ge_of_incomparable {a b : α} (h : Incomparable a b) :
    ¬ b ≼ a :=
  h.right

end Preorder

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

/- Reading and motivation: Identification.lean, Commentary C.2. -/

/-- The share projection is exactly the grade recorded for the weld. -/
@[simp]
theorem share_eq_grade (w : G.Weld) :
    G.share w = G.grade w.agent w.call w.response :=
  rfl

/-- An actual weld witnesses response-function at its own call. -/
theorem mountsAt_of_actual (w : G.Weld) (h : G.Actual w) :
    G.MountsAt w.agent w.call :=
  ⟨w.response, h⟩

/-- An actual weld witnesses response-function somewhere for its agent. -/
theorem mountsSomewhere_of_actual (w : G.Weld) (h : G.Actual w) :
    G.MountsSomewhere w.agent :=
  ⟨w.call, G.mountsAt_of_actual w h⟩

/-- A being with an actual weld is not stone-typed. -/
theorem not_stone_of_actual (w : G.Weld) (h : G.Actual w) :
    ¬ G.Stone w.agent :=
  G.not_stone_of_mountsSomewhere w.agent (G.mountsSomewhere_of_actual w h)

/-- A stone has no actual weld at any call. -/
theorem not_actual_of_stone
    (b : G.Being) (hstone : G.Stone b) {c : G.Call} {r : G.Response} :
    ¬ G.Actual ⟨b, c, r⟩ :=
  fun hactual => hstone c ⟨r, hactual⟩

/-- A stone mounts nowhere. -/
theorem not_mountsSomewhere_of_stone (b : G.Being) (hstone : G.Stone b) :
    ¬ G.MountsSomewhere b :=
  fun hmounts => G.not_stone_of_mountsSomewhere b hmounts hstone

/-- A concrete response at a call rules out stone-typing. -/
theorem not_stone_of_response
    {b : G.Being} {c : G.Call} {r : G.Response}
    (hresp : G.respondsTo b c = some r) :
    ¬ G.Stone b :=
  fun hstone => hstone c ⟨r, hresp⟩

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem atPoleClass_of_stone (b : G.Being) (hstone : G.Stone b) :
    G.AtPoleClass b :=
  Or.inl hstone

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem atPoleClass_of_terminus (b : G.Being) (hterm : G.Terminus b) :
    G.AtPoleClass b :=
  Or.inr hterm

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem atPoleClass_and_not_stone_of_liveTerminus
    (b : G.Being) (h : G.LiveTerminus b) :
    G.AtPoleClass b ∧ ¬ G.Stone b :=
  ⟨G.atPoleClass_of_terminus b h.right, G.liveTerminus_not_stone b h⟩

/-- A responsive terminus is not stone-typed whenever the call-domain has a witness. -/
theorem not_stone_of_responsiveTerminus_of_call
    (b : G.Being) (c : G.Call) (h : G.ResponsiveTerminus b) :
    ¬ G.Stone b :=
  G.liveTerminus_not_stone b (G.responsiveTerminus_live_of_call b c h)

/- Reading and motivation: Identification.lean, Commentary C.2. -/

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem rePitch_tendency_eq_share
    (before : Config Contrib) (received : G.Weld) :
    (G.rePitch before received).tendency = G.share received :=
  rfl

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem isShareDrop_iff_rePitch_tendency_drop
    (before : Config Contrib) (received : G.Weld) :
    G.IsShareDrop before received ↔
      ((G.rePitch before received).tendency ≼ before.tendency ∧
        ¬ (before.tendency ≼ (G.rePitch before received).tendency)) :=
  Iff.rfl

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem rePitch_tendency_le_before_of_shareDrop
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsShareDrop before received) :
    (G.rePitch before received).tendency ≼ before.tendency :=
  h.left

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem not_before_le_rePitch_tendency_of_shareDrop
    {before : Config Contrib} {received : G.Weld}
    (h : G.IsShareDrop before received) :
    ¬ (before.tendency ≼ (G.rePitch before received).tendency) :=
  h.right

/-- A terminus response re-pitches the carried tendency into the pole-class. -/
theorem rePitch_tendency_atBot_of_terminus_response
    (before : Config Contrib) {b : G.Being} {c : G.Call} {r : G.Response}
    (hterm : G.Terminus b) (hresp : G.respondsTo b c = some r) :
    AtBot (G.rePitch before ⟨b, c, r⟩).tendency :=
  G.atBot_of_terminus_response hterm hresp

/- ==============================================================================
   The environs lens
============================================================================== -/

namespace DirectedConvention

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem environsLine_of_shareDropLine
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (h : ShareDropLine G before b deed reception) :
    EnvironsLine G b deed reception :=
  h.left

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem isShareDrop_of_shareDropLine
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (h : ShareDropLine G before b deed reception) :
    G.IsShareDrop before reception :=
  h.right

/-- An environs-line is a delivery-fact. -/
theorem deliveredTo_of_environsLine
    {b : G.Being} {deed reception : G.Weld}
    (h : EnvironsLine G b deed reception) :
    DeliveredTo G deed reception :=
  h.right.right

end DirectedConvention

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem not_isShareDrop_of_tendency_atBot
    {before : Config Contrib} (h : AtBot before.tendency)
    (received : G.Weld) :
    ¬ G.IsShareDrop before received := by
  intro hdrop
  exact hdrop.right (Preorder.le_trans h (shareBot_le (G.share received)))

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem not_isShareDrop_of_eq_shareBot_tendency
    {before : Config Contrib} (h : before.tendency = shareBot)
    (received : G.Weld) :
    ¬ G.IsShareDrop before received :=
  G.not_isShareDrop_of_tendency_atBot (atBot_of_eq_shareBot h) received

namespace DirectedConvention

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem no_shareDropLine_of_tendency_atBot
    {before : Config Contrib} (h : AtBot before.tendency)
    (b : G.Being) (deed reception : G.Weld) :
    ¬ ShareDropLine G before b deed reception :=
  fun hline =>
    G.not_isShareDrop_of_tendency_atBot h reception hline.right

/-- Literal equality with the designated bottom gives the pole-class release
    obstruction. -/
theorem no_shareDropLine_of_eq_shareBot_tendency
    {before : Config Contrib} (h : before.tendency = shareBot)
    (b : G.Being) (deed reception : G.Weld) :
    ¬ ShareDropLine G before b deed reception :=
  no_shareDropLine_of_tendency_atBot G (atBot_of_eq_shareBot h) b deed reception

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem hasShareDropLanding_of_shareDropLine_actual
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (hline : ShareDropLine G before b deed reception)
    (hact : G.Actual reception) :
    HasShareDropLanding G before deed :=
  ⟨reception, ⟨⟨hline.left.right.right, hact⟩, hline.right⟩⟩

/-- Shortfall is closed at a delivered pair when, for any live prior tendency,
    delivery of the deed is enough to yield a share-drop landing for that deed.
    This is regime-relational effectiveness talk, not a nature possessed by a
    being. -/
def ShortfallClosedAt
    (before : Config Contrib) (deed reception : G.Weld) : Prop :=
  ¬ AtBot before.tendency →
    DeliveredTo G deed reception →
      HasShareDropLanding G before deed

/-- An explicit share-drop line with an actual reception supplies the local
    closure predicate. -/
theorem shortfallClosedAt_of_shareDropLine_actual
    {before : Config Contrib} {b : G.Being} {deed reception : G.Weld}
    (hline : ShareDropLine G before b deed reception)
    (hact : G.Actual reception) :
    ShortfallClosedAt G before deed reception :=
  fun _hlive _hdel =>
    hasShareDropLanding_of_shareDropLine_actual G hline hact

/-- Srad faith, stated as a hypothesis: the being is a responsive terminus and
    every delivered reception of one of its deeds closes shortfall for a live
    prior tendency. The universal closure conjunct is exactly the component no
    field-recovery theorem can verify for free. -/
def SradFullyEnlightened (b : G.Being) : Prop :=
  G.ResponsiveTerminus b ∧
    ∀ before deed reception,
      deed.agent = b →
        ShortfallClosedAt G before deed reception

theorem responsiveTerminus_of_sradFullyEnlightened
    {b : G.Being} (h : SradFullyEnlightened G b) :
    G.ResponsiveTerminus b :=
  h.left

theorem shortfallClosedAt_of_sradFullyEnlightened
    {b : G.Being} (h : SradFullyEnlightened G b)
    {before : Config Contrib} {deed reception : G.Weld}
    (hdeed : deed.agent = b) :
    ShortfallClosedAt G before deed reception :=
  h.right before deed reception hdeed

end DirectedConvention

/- Reading and motivation: Identification.lean, Commentary C.2. -/

namespace DirectedConvention

/-- A full reach-back is the same field-side fact as delivery. -/
theorem waaReachBackFull_iff_deliveredTo (deed reception : G.Weld) :
    WaaReachBackFull G deed reception ↔ DeliveredTo G deed reception :=
  Iff.rfl

/-- An aimed call is just delivery, stated from the sowing side. -/
theorem waaAimedAt_iff_deliveredTo (deed reception : G.Weld) :
    WaaAimedAt G deed reception ↔ DeliveredTo G deed reception :=
  Iff.rfl

/-- Landing includes delivery. -/
theorem deliveredTo_of_landsAt
    {deed reception : G.Weld} (h : LandsAt G deed reception) :
    DeliveredTo G deed reception :=
  h.left

/-- Landing includes actuality of the reception. -/
theorem actual_of_landsAt
    {deed reception : G.Weld} (h : LandsAt G deed reception) :
    G.Actual reception :=
  h.right

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem landsAt_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    LandsAt G deed reception :=
  h.left

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem isShareDrop_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    G.IsShareDrop before reception :=
  h.right

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem deliveredTo_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    DeliveredTo G deed reception :=
  deliveredTo_of_landsAt G (landsAt_of_landsWithShareDrop G h)

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem actual_of_landsWithShareDrop
    {before : Config Contrib} {deed reception : G.Weld}
    (h : LandsWithShareDrop G before deed reception) :
    G.Actual reception :=
  actual_of_landsAt G (landsAt_of_landsWithShareDrop G h)

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem exists_landsAt_of_hasShareDropLanding
    {before : Config Contrib} {deed : G.Weld}
    (h : HasShareDropLanding G before deed) :
    ∃ reception, LandsAt G deed reception :=
  h.elim (fun reception hland =>
    ⟨reception, landsAt_of_landsWithShareDrop G hland⟩)

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem exists_actual_reception_of_hasShareDropLanding
    {before : Config Contrib} {deed : G.Weld}
    (h : HasShareDropLanding G before deed) :
    ∃ reception, G.Actual reception :=
  h.elim (fun reception hland =>
    ⟨reception, actual_of_landsWithShareDrop G hland⟩)

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem exists_shareDrop_reception_of_hasShareDropLanding
    {before : Config Contrib} {deed : G.Weld}
    (h : HasShareDropLanding G before deed) :
    ∃ reception, G.IsShareDrop before reception :=
  h.elim (fun reception hland =>
    ⟨reception, isShareDrop_of_landsWithShareDrop G hland⟩)

end DirectedConvention

/- ==============================================================================
   Actual pairs
============================================================================== -/

namespace ReceptionPair

variable {G : Grid Contrib}

/-- The first member of a reception pair is actual. -/
theorem first_actual (p : ReceptionPair G) :
    G.Actual p.first.weld :=
  p.first.actual

/-- The second member of a reception pair is actual. -/
theorem second_actual (p : ReceptionPair G) :
    G.Actual p.second.weld :=
  p.second.actual

/-- The pair's named relation is just delivery from first to second. -/
theorem firstConditionsSecond_iff_deliveredTo (p : ReceptionPair G) :
    p.FirstConditionsSecond ↔
      DirectedConvention.DeliveredTo G p.first.weld p.second.weld :=
  Iff.rfl

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem rePitchSequence_first_tendency
    (before : Config Contrib) (p : ReceptionPair G) :
    (rePitchSequence (G := G) before p).fst.tendency = G.share p.first.weld :=
  rfl

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem rePitchSequence_second_tendency
    (before : Config Contrib) (p : ReceptionPair G) :
    (rePitchSequence (G := G) before p).snd.tendency = G.share p.second.weld :=
  rfl

end ReceptionPair

/- ==============================================================================
   Tiers, utterances, and separate/fuse diagnostics
============================================================================== -/

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem floor_has_no_live_share :
    ¬ Tier.hasLiveShare G (Tier.floor : Tier G) :=
  fun h => h

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem actTime_hasLiveShare_iff_hasSelfPoleIndex (w : G.Weld) :
    Tier.hasLiveShare G (Tier.actTime w) ↔ G.HasSelfPoleIndex w :=
  Iff.rfl

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem not_actTime_hasLiveShare_of_atBot
    {w : G.Weld} (h : AtBot (G.share w)) :
    ¬ Tier.hasLiveShare G (Tier.actTime w) :=
  G.no_self_pole_index_of_atBot w h

/-- Equality with the designated bottom is a bridge into the pole-class
    act-time lemma. -/
theorem not_actTime_hasLiveShare_of_eq_shareBot
    {w : G.Weld} (h : G.share w = shareBot) :
    ¬ Tier.hasLiveShare G (Tier.actTime w) :=
  G.not_actTime_hasLiveShare_of_atBot (atBot_of_eq_shareBot h)

/-- Collapse is impossible at the floor. -/
theorem not_collapse_floor (d : Distinction G) :
    ¬ d.Collapse (Tier.floor : Tier G) :=
  fun hcollapse => G.floor_has_no_live_share hcollapse.left

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem hasLiveShare_of_collapse
    {d : Distinction G} {t : Tier G} (h : d.Collapse t) :
    Tier.hasLiveShare G t :=
  h.left

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem hasLiveShare_of_separated
    {d : Distinction G} {t : Tier G} (h : d.Separated t) :
    Tier.hasLiveShare G t :=
  h.left

/-- Separation rules out collapse at the same tier. -/
theorem not_collapse_of_separated
    {d : Distinction G} {t : Tier G} (h : d.Separated t) :
    ¬ d.Collapse t :=
  fun hcollapse => h.right hcollapse.right

/-- Obeying the rule supplies the fusion clause at every tier. -/
theorem fused_of_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse) (t : Tier G) :
    d.Fused t :=
  h.right t

/- Reading and motivation: Identification.lean, Commentary C.2. -/
theorem separated_of_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse)
    {t : Tier G} (ht : Tier.hasLiveShare G t) :
    d.Separated t :=
  ⟨ht, h.left t ht⟩

/-- Fusion at the floor rules out freeze. -/
theorem not_freeze_of_fused_floor
    {d : Distinction G} (h : d.Fused (Tier.floor : Tier G)) :
    ¬ d.Freeze :=
  fun hfreeze => hfreeze (h G.floor_has_no_live_share)

namespace RecordedUtterance

variable {G : Grid Contrib} {L : ClaimLanguage G}

/-- The answered call is the call carried by the utterance's weld. -/
@[simp]
theorem answersCall_eq_weld_call (u : RecordedUtterance G L) :
    answersCall u = u.weld.call :=
  rfl

/-- Fitting the offered tier is exactly truth at that tier. -/
theorem fitsOfferedTier_iff_trueAt (u : RecordedUtterance G L) :
    FitsOfferedTier u ↔ L.TrueAt u.offeredAt u.content :=
  Iff.rfl

end RecordedUtterance

namespace ErrorGrade

/-- Verdict errors speak in the assertable voice. -/
theorem verdict_voice_assertable :
    ErrorGrade.voice ErrorGrade.verdict = VerdictVoice.assertable :=
  rfl

/-- Shortfall errors speak in the displayable voice. -/
theorem shortfall_voice_displayable :
    ErrorGrade.voice ErrorGrade.shortfall = VerdictVoice.displayable :=
  rfl

end ErrorGrade

namespace DirectedConvention
namespace BeingConvention
namespace GridConvention

/- The lens's own vocabulary: the innermost convention. The abstract
   `ClaimLanguage` machinery remains at `Grid` level; this namespace supplies
   the first concrete rows generated from it. -/

/-- The nested conventions as objects the lens can diagnose claims about. -/
inductive ConventionLayer
  | directedTime
  | beings
  | gridLens

/-- Claims for convention-layer rows. `conventionLive l` says the layer's
    distinction is in force; `layerDenied l` is the deflation. -/
inductive LayerClaim
  | conventionLive (l : ConventionLayer)
  | layerDenied (l : ConventionLayer)

/-- Concrete claim-language for the convention-layer rows. At floor, all
    layer-claims fuse. At live act-time, the convention is live and its denial
    is not. At non-live act-time, neither side is asserted. -/
def layerLanguage (G : Grid Contrib) : ClaimLanguage G where
  Claim := LayerClaim
  Holds
    | .floor, _ => True
    | .actTime w, .conventionLive _ => G.HasSelfPoleIndex w
    | .actTime _, .layerDenied _ => False

def layerRow (G : Grid Contrib) (l : ConventionLayer) : Distinction G :=
  { language := layerLanguage G
    sideA := .conventionLive l
    sideB := .layerDenied l }

def beforeAfterRow (G : Grid Contrib) : Distinction G :=
  layerRow G .directedTime

def beingsRow (G : Grid Contrib) : Distinction G :=
  layerRow G .beings

def gridLensRow (G : Grid Contrib) : Distinction G :=
  layerRow G .gridLens

theorem layerRow_obeys (l : ConventionLayer) :
    (layerRow G l).ObeysSeparateFuse := by
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime w =>
        dsimp [layerRow, layerLanguage, ClaimLanguage.TrueAt]
        intro hiff
        exact hiff.mp hLive
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime w =>
        dsimp [layerRow, layerLanguage, ClaimLanguage.TrueAt]
        constructor
        · intro hLive
          exact hNotLive hLive
        · intro hFalse
          cases hFalse

theorem beforeAfterRow_obeys :
    (beforeAfterRow G).ObeysSeparateFuse :=
  layerRow_obeys G .directedTime

theorem beingsRow_obeys :
    (beingsRow G).ObeysSeparateFuse :=
  layerRow_obeys G .beings

theorem gridLensRow_obeys :
    (gridLensRow G).ObeysSeparateFuse :=
  layerRow_obeys G .gridLens

/-- The deflation can be satisfied only where diagnosis is not live. Offered
    as a live diagnosis, "there is no time" or "there are no beings" is
    refuted by its own tier. -/
theorem layerDenied_holds_only_where_no_live_share
    (l : ConventionLayer) (t : Tier G)
    (h : (layerLanguage G).Holds t (.layerDenied l)) :
    ¬ Tier.hasLiveShare G t := by
  cases t with
  | floor =>
      intro hfloor
      exact hfloor
  | actTime _ =>
      cases h

theorem beforeAfterRow_not_freeze :
    ¬ (beforeAfterRow G).Freeze :=
  Grid.not_freeze_of_obeysSeparateFuse (beforeAfterRow_obeys G)

/-- The before/after collapse is self-refuting at every tier; in particular,
    it cannot be asserted as a live diagnosis. -/
theorem no_time_collapse_self_refuting (t : Tier G) :
    ¬ (beforeAfterRow G).Collapse t :=
  Grid.not_collapse_of_obeysSeparateFuse (beforeAfterRow_obeys G) t

/-- The beings row cannot freeze. The freeze cell in the prose table names the
    position this checked obedience rules out asserting: designation reified
    into ontology against `BeingNegative`. -/
theorem beingsRow_not_freeze :
    ¬ (beingsRow G).Freeze :=
  Grid.not_freeze_of_obeysSeparateFuse (beingsRow_obeys G)

/-- "There are no beings", offered as a live diagnosis, is refuted by its own
    tier. -/
theorem no_beings_collapse_self_refuting (t : Tier G) :
    ¬ (beingsRow G).Collapse t :=
  Grid.not_collapse_of_obeysSeparateFuse (beingsRow_obeys G) t

theorem gridLensRow_not_freeze :
    ¬ (gridLensRow G).Freeze :=
  Grid.not_freeze_of_obeysSeparateFuse (gridLensRow_obeys G)

theorem lens_denial_collapse_self_refuting (t : Tier G) :
    ¬ (gridLensRow G).Collapse t :=
  Grid.not_collapse_of_obeysSeparateFuse (gridLensRow_obeys G) t

/- --------------------------------------------------------------------------
   Content-bearing layer rows
-------------------------------------------------------------------------- -/

/-- Content-bearing language for the same layer claims. The convention-live
    side is still the live-share condition; the denial side now has content
    specific to the row. -/
def contentLayerLanguage (G : Grid Contrib) : ClaimLanguage G where
  Claim := LayerClaim
  Holds
    | .floor, _ => True
    | .actTime w, .conventionLive _ => G.HasSelfPoleIndex w
    | .actTime _, .layerDenied .directedTime => DirectionVoid Contrib
    | .actTime _, .layerDenied .beings => G.AllStone
    | .actTime _, .layerDenied .gridLens => ∀ t : Tier G, ¬ Tier.hasLiveShare G t

def contentLayerRow (G : Grid Contrib) (l : ConventionLayer) : Distinction G :=
  { language := contentLayerLanguage G
    sideA := .conventionLive l
    sideB := .layerDenied l }

def contentBeforeAfterRow (G : Grid Contrib) : Distinction G :=
  contentLayerRow G .directedTime

def contentBeingsRow (G : Grid Contrib) : Distinction G :=
  contentLayerRow G .beings

def contentGridLensRow (G : Grid Contrib) : Distinction G :=
  contentLayerRow G .gridLens

theorem contentLayerRow_obeys_of_direction
    (h : ∃ a b : Contrib, Strict a b) :
    (contentLayerRow G .directedTime).ObeysSeparateFuse := by
  rcases h with ⟨a, b, hstrict⟩
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        intro hiff
        exact (hiff.mp hLive) a b hstrict
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        constructor
        · intro hLive
          exact False.elim (hNotLive hLive)
        · intro hvoid
          exact False.elim (hvoid a b hstrict)

theorem contentLayerRow_obeys_of_being
    (h : ∃ b : G.Being, ¬ G.Stone b) :
    (contentLayerRow G .beings).ObeysSeparateFuse := by
  rcases h with ⟨b, hnotStone⟩
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        intro hiff
        exact hnotStone ((hiff.mp hLive) b)
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        constructor
        · intro hLive
          exact False.elim (hNotLive hLive)
        · intro hall
          exact False.elim (hnotStone (hall b))

theorem contentLayerRow_obeys_of_liveTier
    (h : ∃ t : Tier G, Tier.hasLiveShare G t) :
    (contentLayerRow G .gridLens).ObeysSeparateFuse := by
  rcases h with ⟨liveTier, hLiveTier⟩
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        intro hiff
        exact (hiff.mp hLive) liveTier hLiveTier
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [contentLayerRow, contentLayerLanguage, ClaimLanguage.TrueAt]
        constructor
        · intro hLive
          exact False.elim (hNotLive hLive)
        · intro hnoLive
          exact False.elim (hnoLive liveTier hLiveTier)

theorem contentBeforeAfterRow_obeys_of_direction
    (h : ∃ a b : Contrib, Strict a b) :
    (contentBeforeAfterRow G).ObeysSeparateFuse :=
  contentLayerRow_obeys_of_direction G h

theorem contentBeingsRow_obeys_of_being
    (h : ∃ b : G.Being, ¬ G.Stone b) :
    (contentBeingsRow G).ObeysSeparateFuse :=
  contentLayerRow_obeys_of_being G h

theorem contentGridLensRow_obeys_of_liveTier
    (h : ∃ t : Tier G, Tier.hasLiveShare G t) :
    (contentGridLensRow G).ObeysSeparateFuse :=
  contentLayerRow_obeys_of_liveTier G h

/-- An actual utterance of the beings-denial cannot fit an act-time tier:
    the utterer's actual response supplies a non-stone witness. -/
theorem beings_denial_fits_only_floor
    (u : RecordedUtterance G (contentLayerLanguage G))
    (hc : u.content = .layerDenied .beings)
    (w' : G.Weld) (ht : u.offeredAt = .actTime w') :
    ¬ u.FitsOfferedTier := by
  intro hfit
  change (contentLayerLanguage G).TrueAt u.offeredAt u.content at hfit
  rw [ht, hc] at hfit
  dsimp [contentLayerLanguage, ClaimLanguage.TrueAt] at hfit
  exact (G.not_stone_of_actual u.weld u.actual) (hfit u.weld.agent)

/-- A directed-time denial offered by an appropriating utterer cannot fit an
    act-time tier: the utterer's live share is itself a strict direction. -/
theorem time_denial_unfit_for_appropriating_utterer
    (u : RecordedUtterance G (contentLayerLanguage G))
    (hc : u.content = .layerDenied .directedTime)
    (hidx : G.HasSelfPoleIndex u.weld)
    (w' : G.Weld) (ht : u.offeredAt = .actTime w') :
    ¬ u.FitsOfferedTier := by
  intro hfit
  change (contentLayerLanguage G).TrueAt u.offeredAt u.content at hfit
  rw [ht, hc] at hfit
  dsimp [contentLayerLanguage, ClaimLanguage.TrueAt] at hfit
  exact hfit (shareBot : Contrib) (G.share u.weld)
    (G.strict_shareBot_of_hasSelfPoleIndex u.weld hidx)

/- --------------------------------------------------------------------------
   Re-emptying ladder
-------------------------------------------------------------------------- -/

/-- The two sides used to re-empty a distinction. Deliberately, neither side
    quantifies over ladder levels; level-quantification stays in meta-theorems. -/
inductive LadderSide
  | liveBelow
  | finalBelow

/-- Re-empty a distinction: the new row separates the lower row's live
    separation from the claim that the lower row survives the floor. -/
def reEmptied {G : Grid Contrib} (d : Distinction G) : Distinction G where
  language :=
    { Claim := LadderSide
      Holds := fun t c =>
        match t, c with
        | .floor, _ => True
        | .actTime w, .liveBelow => d.Separated (.actTime w)
        | .actTime _, .finalBelow => d.Freeze }
  sideA := .liveBelow
  sideB := .finalBelow

def ladder {G : Grid Contrib} (d : Distinction G) : Nat → Distinction G
  | 0 => d
  | n + 1 => reEmptied (ladder d n)

theorem reEmptied_obeysSeparateFuse
    {d : Distinction G} (h : d.ObeysSeparateFuse) :
    (reEmptied d).ObeysSeparateFuse := by
  constructor
  · intro t hLive
    cases t with
    | floor =>
        cases hLive
    | actTime _ =>
        dsimp [reEmptied, ClaimLanguage.TrueAt]
        intro hiff
        exact (Grid.not_freeze_of_obeysSeparateFuse h)
          (hiff.mp (G.separated_of_obeysSeparateFuse h hLive))
  · intro t hNotLive
    cases t with
    | floor =>
        constructor <;> intro _ <;> exact True.intro
    | actTime _ =>
        dsimp [reEmptied, ClaimLanguage.TrueAt]
        constructor
        · intro hsep
          exact False.elim (hNotLive hsep.left)
        · intro hfreeze
          exact False.elim ((Grid.not_freeze_of_obeysSeparateFuse h) hfreeze)

theorem ladder_obeys {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ∀ n, (ladder d n).ObeysSeparateFuse := by
  intro n
  induction n with
  | zero =>
      exact h
  | succ _ ih =>
      exact reEmptied_obeysSeparateFuse (G := G) ih

theorem no_level_final {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ∀ n, ¬ (ladder d n).Freeze := by
  intro n
  exact Grid.not_freeze_of_obeysSeparateFuse (ladder_obeys (G := G) h n)

theorem ladder_collapse_self_refuting
    {d : Distinction G} (h : d.ObeysSeparateFuse) :
    ∀ n t, ¬ (ladder d n).Collapse t := by
  intro n t
  exact Grid.not_collapse_of_obeysSeparateFuse (ladder_obeys (G := G) h n) t

def beingsLadder (G : Grid Contrib) : Nat → Distinction G :=
  ladder (beingsRow G)

def contentBeingsLadder (G : Grid Contrib) : Nat → Distinction G :=
  ladder (contentBeingsRow G)

theorem beingsLadder_obeys :
    ∀ n, (beingsLadder G n).ObeysSeparateFuse :=
  ladder_obeys (G := G) (beingsRow_obeys G)

theorem beingsLadder_no_level_final :
    ∀ n, ¬ (beingsLadder G n).Freeze :=
  no_level_final (G := G) (beingsRow_obeys G)

theorem contentBeingsLadder_obeys_of_being
    (h : ∃ b : G.Being, ¬ G.Stone b) :
    ∀ n, (contentBeingsLadder G n).ObeysSeparateFuse :=
  ladder_obeys (G := G) (contentBeingsRow_obeys_of_being G h)

theorem contentBeingsLadder_no_level_final_of_being
    (h : ∃ b : G.Being, ¬ G.Stone b) :
    ∀ n, ¬ (contentBeingsLadder G n).Freeze :=
  no_level_final (G := G) (contentBeingsRow_obeys_of_being G h)

end GridConvention
end BeingConvention
end DirectedConvention

end Grid

end WAA
