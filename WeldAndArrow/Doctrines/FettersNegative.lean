/-
================================================================================
  WeldAndArrow.Doctrines.FettersNegative
  Fresh-call underdetermination for run-assigned fetter tags
================================================================================
-/

import WeldAndArrow.Doctrines.Fetters

namespace WAA

namespace FettersNegative

open Grid.DirectedConvention.BeingConvention

inductive Being
  | practitioner

inductive Call
  | seen
  | fresh
deriving DecidableEq

inductive Response
  | response

/-- The seen call is quiet; the fresh call is quiet too. -/
def quietGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade _ _ _ := 0
  conditions _ _ := True

/-- The same seen behavior, but the fresh call carries live share. -/
def freshClenchGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade _ c _ :=
    match c with
    | .seen => 0
    | .fresh => 5
  conditions _ _ := True

def quietPath : quietGrid.PathScheme where
  proj _ := Path.streamEntry

def freshPath : freshClenchGrid.PathScheme where
  proj _ := Path.streamEntry

/-- Identity-view provocations are modeled here as the whole call domain. -/
def quietReading : quietGrid.FetterReading where
  provocationClass
    | Fetter.identityView, _ => True
    | _, _ => False

def freshReading : freshClenchGrid.FetterReading where
  provocationClass
    | Fetter.identityView, _ => True
    | _, _ => False

def quietSeen : quietGrid.Weld :=
  ⟨Being.practitioner, Call.seen, Response.response⟩

def freshSeen : freshClenchGrid.Weld :=
  ⟨Being.practitioner, Call.seen, Response.response⟩

def freshWeld : freshClenchGrid.Weld :=
  ⟨Being.practitioner, Call.fresh, Response.response⟩

def quietRun : List quietGrid.Weld :=
  [quietSeen]

def freshRun : List freshClenchGrid.Weld :=
  [freshSeen]

/-- The restricted seen track record: response and grade behavior on `seen`. -/
abbrev TrackData : Type :=
  Option Response × (Response → Nat)

def quietSeenTrackData : TrackData :=
  (quietGrid.respondsTo Being.practitioner Call.seen,
    fun r => quietGrid.grade Being.practitioner Call.seen r)

def freshSeenTrackData : TrackData :=
  (freshClenchGrid.respondsTo Being.practitioner Call.seen,
    fun r => freshClenchGrid.grade Being.practitioner Call.seen r)

theorem seen_track_agrees :
    quietSeenTrackData = freshSeenTrackData :=
  rfl

theorem quiet_seen_runQuiet :
    quietGrid.RunQuiet quietPath Path.streamEntry
      (quietReading.provocationClass Fetter.identityView) quietRun := by
  intro w hmem _hactual _hfiber _hclass
  simp [quietRun, quietSeen] at hmem
  subst w
  dsimp [Grid.share, quietGrid, AtBot, shareBot]
  show (0 : Nat) ≤ 0
  decide

theorem fresh_seen_runQuiet :
    freshClenchGrid.RunQuiet freshPath Path.streamEntry
      (freshReading.provocationClass Fetter.identityView) freshRun := by
  intro w hmem _hactual _hfiber _hclass
  simp [freshRun, freshSeen] at hmem
  subst w
  dsimp [Grid.share, freshClenchGrid, AtBot, shareBot]
  show (0 : Nat) ≤ 0
  decide

theorem quiet_fetterCut :
    quietGrid.FetterCut quietPath Path.streamEntry quietReading
      Fetter.identityView := by
  intro w _hactual _hfiber _hclass
  dsimp [Grid.share, quietGrid, AtBot, shareBot]
  show (0 : Nat) ≤ 0
  decide

theorem fresh_not_fetterCut :
    ¬ freshClenchGrid.FetterCut freshPath Path.streamEntry freshReading
      Fetter.identityView := by
  intro hcut
  have hbot : AtBot (freshClenchGrid.share freshWeld) :=
    hcut freshWeld rfl rfl True.intro
  dsimp [Grid.share, freshClenchGrid, freshWeld, AtBot, shareBot] at hbot
  exact Nat.not_succ_le_zero 4 hbot

theorem fresh_share_disagrees :
    quietGrid.grade Being.practitioner Call.fresh Response.response ≠
      freshClenchGrid.grade Being.practitioner Call.fresh Response.response := by
  decide

/-- A finite seen class-quiet track does not determine the fresh call. -/
theorem seen_run_underdetermines_fetterCut :
    quietSeenTrackData = freshSeenTrackData ∧
      quietGrid.RunQuiet quietPath Path.streamEntry
        (quietReading.provocationClass Fetter.identityView) quietRun ∧
      freshClenchGrid.RunQuiet freshPath Path.streamEntry
        (freshReading.provocationClass Fetter.identityView) freshRun ∧
      quietGrid.FetterCut quietPath Path.streamEntry quietReading
        Fetter.identityView ∧
      ¬ freshClenchGrid.FetterCut freshPath Path.streamEntry freshReading
        Fetter.identityView :=
  ⟨seen_track_agrees, quiet_seen_runQuiet, fresh_seen_runQuiet,
    quiet_fetterCut, fresh_not_fetterCut⟩

end FettersNegative

end WAA
