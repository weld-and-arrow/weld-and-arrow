/-
================================================================================
  WeldAndArrow.Doctrines.EffectiveTerminusNegative
  Actual-run underdetermination of effective termination
================================================================================

The standing predicate is intentionally stronger than any actual-run transcript
that omits the delivery register. Replacing only `conditions` can leave every
mounted response and share unchanged while flipping `WaaEffectiveTerminus`.

Reading and motivation: Identification/Commentary.lean, C.4.
-/

import WeldAndArrow.Doctrines.Shusho
import WeldAndArrow.Doctrines.SraddhaNegative

namespace WAA

namespace EffectiveTerminusNegative

open Grid
open Grid.DirectedConvention

abbrev baseGrid : Grid Nat :=
  SraddhaNegative.zeroEffectGrid

abbrev sealedGrid : Grid Nat :=
  baseGrid.withConditions (fun _ _ => False)

def addedDelivery (deed reception : sealedGrid.Weld) : Prop :=
  deed.agent = SraddhaNegative.Being.sraddha ∧
    reception.agent = SraddhaNegative.Being.receiver

abbrev openedGrid : Grid Nat :=
  sealedGrid.withConditions addedDelivery

def b : sealedGrid.Being :=
  SraddhaNegative.Being.sraddha

def liveBefore : Config Nat :=
  SraddhaNegative.liveBefore

def deed : sealedGrid.Weld :=
  ⟨SraddhaNegative.Being.sraddha,
    SraddhaNegative.Call.call,
    SraddhaNegative.Response.response⟩

def reception : sealedGrid.Weld :=
  ⟨SraddhaNegative.Being.receiver,
    SraddhaNegative.Call.call,
    SraddhaNegative.Response.response⟩

theorem sealed_responsiveTerminus :
    sealedGrid.ResponsiveTerminus b := by
  constructor
  · intro _c
    exact ⟨SraddhaNegative.Response.response, rfl⟩
  · intro _c _r _hresp
    exact Nat.le_refl 0

theorem sealed_undelivered :
    ∀ (deed reception : sealedGrid.Weld),
      deed.agent = b → ¬ DeliveredTo sealedGrid deed reception := by
  intro deed reception _hdeed hdel
  exact hdel

theorem sealed_waaEffectiveTerminus :
    WaaEffectiveTerminus sealedGrid b :=
  waaEffectiveTerminus_of_responsiveTerminus_of_undelivered
    sealedGrid sealed_responsiveTerminus sealed_undelivered

theorem opened_delivered :
    DeliveredTo openedGrid deed reception := by
  exact ⟨rfl, rfl⟩

theorem opened_liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency :=
  SraddhaNegative.liveBefore_not_atBot

theorem opened_not_hasShareDropLanding :
    ¬ HasShareDropLanding openedGrid liveBefore deed := by
  rintro ⟨received, hland⟩
  have hreceiver : received.agent = SraddhaNegative.Being.receiver :=
    hland.left.left.right
  have hdrop : Strict (openedGrid.share received) liveBefore.tendency :=
    hland.right
  have hstrict : Strict (1 : Nat) 1 := by
    simpa [openedGrid, sealedGrid, baseGrid, Grid.withConditions, Grid.share,
      SraddhaNegative.zeroEffectGrid, liveBefore, SraddhaNegative.liveBefore,
      hreceiver] using hdrop
  exact strict_irrefl (1 : Nat) hstrict

theorem opened_not_waaEffectiveTerminus :
    ¬ WaaEffectiveTerminus openedGrid b := by
  intro hstanding
  exact opened_not_hasShareDropLanding
    (hstanding.right liveBefore deed reception rfl
      opened_liveBefore_not_atBot opened_delivered)

/-- The actual-run transcript used by this collision: response function plus
    grade/share data, deliberately excluding the delivery relation. -/
abbrev RunData : Type :=
  (SraddhaNegative.Being -> SraddhaNegative.Call ->
      Option SraddhaNegative.Response) ×
    (SraddhaNegative.Being -> SraddhaNegative.Call ->
      SraddhaNegative.Response -> Nat)

def sealedRunData : RunData :=
  (sealedGrid.respondsTo, sealedGrid.grade)

def openedRunData : RunData :=
  (openedGrid.respondsTo, openedGrid.grade)

theorem runData_agrees :
    sealedRunData = openedRunData :=
  rfl

theorem actual_iff_agrees (w : sealedGrid.Weld) :
    sealedGrid.Actual w ↔ openedGrid.Actual w :=
  Iff.rfl

theorem share_agrees (w : sealedGrid.Weld) :
    sealedGrid.share w = openedGrid.share w :=
  rfl

theorem respondsTo_agrees (being : sealedGrid.Being) (cue : sealedGrid.Call) :
    sealedGrid.respondsTo being cue = openedGrid.respondsTo being cue :=
  rfl

theorem effectiveTerminus_collision :
    sealedRunData = openedRunData ∧
      WaaEffectiveTerminus sealedGrid b ∧
        ¬ WaaEffectiveTerminus openedGrid b :=
  ⟨runData_agrees, sealed_waaEffectiveTerminus,
    opened_not_waaEffectiveTerminus⟩

/-- No Boolean estimator from this actual-run transcript can recover the
    effective-terminus predicate across the collision. -/
theorem no_effectiveTerminus_recovery_from_run :
    ¬ ∃ estimate : RunData -> Bool,
        estimate sealedRunData = true ∧
          estimate openedRunData = false := by
  rintro ⟨estimate, hsealed, hopened⟩
  have hsame : estimate sealedRunData = estimate openedRunData :=
    congrArg estimate runData_agrees
  have htruefalse : true = false := by
    calc
      true = estimate sealedRunData := hsealed.symm
      _ = estimate openedRunData := hsame
      _ = false := hopened
  cases htruefalse

theorem actual_run_data_underdetermines_effectiveTerminus :
    WaaEffectiveTerminus sealedGrid b ∧
      ¬ WaaEffectiveTerminus openedGrid b ∧
        sealedRunData = openedRunData ∧
          ¬ ∃ estimate : RunData -> Bool,
            estimate sealedRunData = true ∧
              estimate openedRunData = false :=
  ⟨sealed_waaEffectiveTerminus, opened_not_waaEffectiveTerminus,
    runData_agrees, no_effectiveTerminus_recovery_from_run⟩

end EffectiveTerminusNegative

end WAA
