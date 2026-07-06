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

theorem quiet_seen_runQuietWithin :
    quietGrid.RunQuietWithin quietPath Path.streamEntry
      (quietReading.provocationClass Fetter.identityView)
      (fun _ => True) quietRun := by
  intro w hmem hactual hfiber hclass _htag
  exact quiet_seen_runQuiet w hmem hactual hfiber hclass

theorem fresh_seen_runQuietWithin :
    freshClenchGrid.RunQuietWithin freshPath Path.streamEntry
      (freshReading.provocationClass Fetter.identityView)
      (fun _ => True) freshRun := by
  intro w hmem hactual hfiber hclass _htag
  exact fresh_seen_runQuiet w hmem hactual hfiber hclass

theorem quiet_fetterCutWithin :
    quietGrid.FetterCutWithin quietPath Path.streamEntry quietReading
      Fetter.identityView (fun _ => True) := by
  intro w hactual hfiber hclass _htag
  exact quiet_fetterCut w hactual hfiber hclass

theorem fresh_not_fetterCutWithin :
    ¬ freshClenchGrid.FetterCutWithin freshPath Path.streamEntry freshReading
      Fetter.identityView (fun _ => True) := by
  intro hcut
  have hbot : AtBot (freshClenchGrid.share freshWeld) :=
    hcut freshWeld rfl rfl True.intro True.intro
  dsimp [Grid.share, freshClenchGrid, freshWeld, AtBot, shareBot] at hbot
  exact Nat.not_succ_le_zero 4 hbot

/-- A finite seen class-quiet track in a tag-region does not determine the
    fresh call. The tag class is total here, so the old fresh-call obstruction
    transfers directly to the product predicate. -/
theorem seen_run_underdetermines_fetterCutWithin :
    quietSeenTrackData = freshSeenTrackData ∧
      quietGrid.RunQuietWithin quietPath Path.streamEntry
        (quietReading.provocationClass Fetter.identityView)
        (fun _ => True) quietRun ∧
      freshClenchGrid.RunQuietWithin freshPath Path.streamEntry
        (freshReading.provocationClass Fetter.identityView)
        (fun _ => True) freshRun ∧
      quietGrid.FetterCutWithin quietPath Path.streamEntry quietReading
        Fetter.identityView (fun _ => True) ∧
      ¬ freshClenchGrid.FetterCutWithin freshPath Path.streamEntry freshReading
        Fetter.identityView (fun _ => True) :=
  ⟨seen_track_agrees, quiet_seen_runQuietWithin, fresh_seen_runQuietWithin,
    quiet_fetterCutWithin, fresh_not_fetterCutWithin⟩

/- ==============================================================================
   No grid-carried recovery of a unique soma boundary
============================================================================== -/

/-- Two fine tags with identical grid data and incompatible region readings. -/
def somaGrid : Grid Nat where
  Being      := Bool
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := True

def somaMergeReading : somaGrid.SomaReading where
  speechThoughtTag _ := True

def somaSplitReading : somaGrid.SomaReading where
  speechThoughtTag p := p = false

theorem somaMerge_true_in_region :
    somaMergeReading.speechThoughtTag true :=
  True.intro

theorem somaSplit_true_not_in_region :
    ¬ somaSplitReading.speechThoughtTag true := by
  intro h
  cases h

abbrev SomaW := RawWeld Bool Unit Unit

abbrev SomaGridData : Type :=
  (Bool → Unit → Option Unit) ×
    (Bool → Unit → Unit → Nat) ×
      (SomaW → SomaW → Prop)

def somaGridData : SomaGridData :=
  (somaGrid.respondsTo, somaGrid.grade, somaGrid.conditions)

def mergedRegion (_p : Bool) : Prop := True

def splitRegion (p : Bool) : Prop := p = false

/-- The same grid data supports incompatible supplied soma-readings. Holding a
    speech/thought region as recovered from the grid is the uniform freeze on
    the tag axis. -/
theorem no_region_boundary_recovery :
    ¬ ∃ recover : SomaGridData → Bool → Prop,
        recover somaGridData = mergedRegion ∧
        recover somaGridData = splitRegion := by
  rintro ⟨recover, hmerge, hsplit⟩
  have hmerged : recover somaGridData true := by
    rw [hmerge]
    exact True.intro
  have hsplitNot : ¬ recover somaGridData true := by
    rw [hsplit]
    intro h
    cases h
  exact hsplitNot hmerged

theorem soma_boundary_underdetermined :
    somaMergeReading.speechThoughtTag true ∧
      ¬ somaSplitReading.speechThoughtTag true ∧
        ¬ ∃ recover : SomaGridData → Bool → Prop,
          recover somaGridData = mergedRegion ∧
            recover somaGridData = splitRegion :=
  ⟨somaMerge_true_in_region, somaSplit_true_not_in_region,
    no_region_boundary_recovery⟩

end FettersNegative

end WAA
