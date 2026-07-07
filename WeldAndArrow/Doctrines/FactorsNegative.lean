/-
================================================================================
  WeldAndArrow.Doctrines.FactorsNegative
  Negative witnesses for factor readings
================================================================================
-/

import WeldAndArrow.Doctrines.Factors
import WeldAndArrow.Doctrines.CorrelationsNegative

namespace WAA

namespace FactorsNegative

open Grid.DirectedConvention
open Grid.DirectedConvention.BeingConvention

/- ==============================================================================
   Hold/conceit boundary recovery
============================================================================== -/

def holdConceitGrid : Grid Nat where
  Being      := Unit
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 1
  conditions _ _ := True

def holdConceitCoarsening : BeingCoarsening holdConceitGrid Unit where
  proj _ := ()

def factorHoldReading : holdConceitGrid.FetterReading where
  provocationClass
    | Fetter.identityView, _ => True
    | _, _ => False

def conceitReading : holdConceitGrid.FetterReading where
  provocationClass
    | Fetter.conceit, _ => True
    | _, _ => False

def holdConceitWeld : holdConceitGrid.Weld :=
  ⟨(), (), ()⟩

def holdConceitRun : List holdConceitGrid.Weld :=
  [holdConceitWeld]

theorem factor_reading_holds_view :
    holdConceitGrid.FactorHeld holdConceitCoarsening ()
      factorHoldReading PathFactor.view holdConceitRun := by
  refine ⟨holdConceitWeld, ?_, rfl, rfl, ?_, ?_⟩
  · simp [holdConceitRun]
  · exact Or.inl True.intro
  · dsimp [Grid.HasSelfPoleIndex, Grid.share, holdConceitGrid,
      holdConceitWeld, AtBot, shareBot]
    change ¬ (1 : Nat) ≤ 0
    exact Nat.not_succ_le_zero 0

theorem conceit_reading_live :
    ∃ w ∈ holdConceitRun,
      holdConceitGrid.Actual w ∧
        holdConceitCoarsening.InFiber () w ∧
        conceitReading.provocationClass Fetter.conceit w.call ∧
        holdConceitGrid.HasSelfPoleIndex w := by
  refine ⟨holdConceitWeld, ?_, rfl, rfl, True.intro, ?_⟩
  · simp [holdConceitRun]
  · dsimp [Grid.HasSelfPoleIndex, Grid.share, holdConceitGrid,
      holdConceitWeld, AtBot, shareBot]
    change ¬ (1 : Nat) ≤ 0
    exact Nat.not_succ_le_zero 0

abbrev HoldConceitGridData : Type :=
  (Unit → Unit → Option Unit) ×
    (Unit → Unit → Unit → Nat) ×
      (holdConceitGrid.Weld → holdConceitGrid.Weld → Prop)

def holdConceitGridData : HoldConceitGridData :=
  (holdConceitGrid.respondsTo, holdConceitGrid.grade,
    holdConceitGrid.conditions)

def factorHoldBoundary (_c : Unit) : Prop :=
  True

def conceitAsHoldBoundary (_c : Unit) : Prop :=
  False

/-- The same response/grade/share data support a live factor-hold reading and
    a live conceit reading. No function of the shared grid data recovers which
    boundary is in force; the hold/conceit line is supplied diagnosis-time
    data. -/
theorem no_hold_conceit_boundary_recovery :
    ¬ ∃ recover : HoldConceitGridData → Unit → Prop,
        recover holdConceitGridData = factorHoldBoundary ∧
        recover holdConceitGridData = conceitAsHoldBoundary := by
  rintro ⟨recover, hfactor, hconceit⟩
  have hheld : recover holdConceitGridData () := by
    rw [hfactor]
    exact True.intro
  have hnotHeld : ¬ recover holdConceitGridData () := by
    rw [hconceit]
    intro h
    cases h
  exact hnotHeld hheld

theorem hold_conceit_boundary_underdetermined :
    holdConceitGrid.FactorHeld holdConceitCoarsening ()
      factorHoldReading PathFactor.view holdConceitRun ∧
      (∃ w ∈ holdConceitRun,
        holdConceitGrid.Actual w ∧
          holdConceitCoarsening.InFiber () w ∧
          conceitReading.provocationClass Fetter.conceit w.call ∧
          holdConceitGrid.HasSelfPoleIndex w) ∧
      ¬ ∃ recover : HoldConceitGridData → Unit → Prop,
        recover holdConceitGridData = factorHoldBoundary ∧
          recover holdConceitGridData = conceitAsHoldBoundary :=
  ⟨factor_reading_holds_view, conceit_reading_live,
    no_hold_conceit_boundary_recovery⟩

/- ==============================================================================
   Factor-order underdetermination
============================================================================== -/

inductive OrderCall
  | rites
  | first
  | second

inductive OrderResponse
  | response

def factorOrderGrid : Grid Nat where
  Being      := Unit
  Call       := OrderCall
  Response   := OrderResponse
  respondsTo _ _ := some OrderResponse.response
  grade _ c _ :=
    match c with
    | OrderCall.rites => 3
    | OrderCall.first => 2
    | OrderCall.second => 1
  conditions _ _ := True

def orderRitesWeld : factorOrderGrid.Weld :=
  ⟨(), OrderCall.rites, OrderResponse.response⟩

def orderFirstWeld : factorOrderGrid.Weld :=
  ⟨(), OrderCall.first, OrderResponse.response⟩

def orderSecondWeld : factorOrderGrid.Weld :=
  ⟨(), OrderCall.second, OrderResponse.response⟩

def orderRitesRun : List factorOrderGrid.Weld :=
  [orderRitesWeld]

def orderFirstRun : List factorOrderGrid.Weld :=
  [orderFirstWeld]

def orderSecondRun : List factorOrderGrid.Weld :=
  [orderSecondWeld]

def orderRuns : List (List factorOrderGrid.Weld) :=
  [orderRitesRun, orderFirstRun, orderSecondRun]

def orderSerialReading : factorOrderGrid.FetterReading where
  provocationClass
    | Fetter.ritesGrasp, OrderCall.rites => True
    | Fetter.identityView, OrderCall.first => True
    | Fetter.sensualDesire, OrderCall.second => True
    | _, _ => False

def orderReversedReading : factorOrderGrid.FetterReading where
  provocationClass
    | Fetter.ritesGrasp, OrderCall.rites => True
    | Fetter.identityView, OrderCall.second => True
    | Fetter.sensualDesire, OrderCall.first => True
    | _, _ => False

abbrev FactorOrderSeenData : Type :=
  (Unit → OrderCall → Option OrderResponse) ×
    (Unit → OrderCall → OrderResponse → Nat)

def serialOrderSeenData : FactorOrderSeenData :=
  (factorOrderGrid.respondsTo, factorOrderGrid.grade)

def reversedOrderSeenData : FactorOrderSeenData :=
  (factorOrderGrid.respondsTo, factorOrderGrid.grade)

theorem orderRites_shareDrop_serial :
    factorOrderGrid.ShareDropRunOnFactor orderSerialReading
      PathFactor.rites orderRitesRun := by
  refine ⟨{ tendency := 5 }, ?_⟩
  constructor
  · refine Grid.ShareDropRun.cons ?_ ?_ ?_
    · rfl
    · dsimp [Grid.IsShareDrop, Grid.share, factorOrderGrid,
        orderRitesWeld]
      constructor
      · change (3 : Nat) ≤ 5
        decide
      · change ¬ (5 : Nat) ≤ 3
        decide
    · exact Grid.ShareDropRun.nil _
  · intro w hmem
    simp [orderRitesRun] at hmem
    subst w
    exact True.intro

theorem orderView_shareDrop_serial :
    factorOrderGrid.ShareDropRunOnFactor orderSerialReading
      PathFactor.view orderFirstRun := by
  refine ⟨{ tendency := 5 }, ?_⟩
  constructor
  · refine Grid.ShareDropRun.cons ?_ ?_ ?_
    · rfl
    · dsimp [Grid.IsShareDrop, Grid.share, factorOrderGrid,
        orderFirstWeld]
      constructor
      · change (2 : Nat) ≤ 5
        decide
      · change ¬ (5 : Nat) ≤ 2
        decide
    · exact Grid.ShareDropRun.nil _
  · intro w hmem
    simp [orderFirstRun] at hmem
    subst w
    exact Or.inl True.intro

theorem orderResolve_shareDrop_serial :
    factorOrderGrid.ShareDropRunOnFactor orderSerialReading
      PathFactor.resolve orderSecondRun := by
  refine ⟨{ tendency := 5 }, ?_⟩
  constructor
  · refine Grid.ShareDropRun.cons ?_ ?_ ?_
    · rfl
    · dsimp [Grid.IsShareDrop, Grid.share, factorOrderGrid,
        orderSecondWeld]
      constructor
      · change (1 : Nat) ≤ 5
        decide
      · change ¬ (5 : Nat) ≤ 1
        decide
    · exact Grid.ShareDropRun.nil _
  · intro w hmem
    simp [orderSecondRun] at hmem
    subst w
    exact Or.inl True.intro

theorem orderSerial_runsExhibit :
    factorOrderGrid.RunsExhibitFactorOrder orderSerialReading orderRuns := by
  exact ⟨orderRitesRun, orderFirstRun, orderSecondRun, rfl,
    orderRites_shareDrop_serial, orderView_shareDrop_serial,
    orderResolve_shareDrop_serial⟩

theorem orderReversed_not_runsExhibit :
    ¬ factorOrderGrid.RunsExhibitFactorOrder orderReversedReading
      orderRuns := by
  rintro ⟨ritesRun, viewRun, resolveRun, hseq, _hrites, hview, _hresolve⟩
  dsimp [orderRuns] at hseq
  cases hseq
  rcases hview with ⟨_before, _hdrop, hall⟩
  have hclass :
      PathFactor.blockerClass orderReversedReading PathFactor.view
        orderFirstWeld.call :=
    hall orderFirstWeld (by simp [orderFirstRun])
  dsimp [PathFactor.blockerClass, orderReversedReading, orderFirstWeld]
    at hclass
  rcases hclass with hclass | hclass <;> cases hclass

/-- The same seen response and grade data do not determine the factor order:
    one supplied reading sees the runs as rites-before-view-before-resolve,
    while another reverses the view/resolve diagnosis on the same calls. -/
theorem seen_run_underdetermines_factorOrder :
    serialOrderSeenData = reversedOrderSeenData ∧
      factorOrderGrid.RunsExhibitFactorOrder orderSerialReading orderRuns ∧
      ¬ factorOrderGrid.RunsExhibitFactorOrder orderReversedReading
        orderRuns :=
  ⟨rfl, orderSerial_runsExhibit, orderReversed_not_runsExhibit⟩

/- ==============================================================================
   Lineage-switching witness
============================================================================== -/

inductive LineageStage
  | theravada (p : Path)
  | bulls (b : Grid.BullStage)

def lineageGrid : Grid Nat where
  Being      := Unit
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions _ _ := True

def lineageWeld : lineageGrid.Weld :=
  ⟨(), (), ()⟩

def lineageRun : List lineageGrid.Weld :=
  [lineageWeld]

def theravadaFactorScheme : lineageGrid.StageScheme LineageStage where
  proj _ := LineageStage.theravada Path.onceReturn

def bullsLineageScheme : lineageGrid.StageScheme LineageStage where
  proj _ := LineageStage.bulls Grid.BullStage.taming

abbrev LineageSeenData : Type :=
  (Unit → Unit → Option Unit) × (Unit → Unit → Unit → Nat)

def lineageSeenData : LineageSeenData :=
  (lineageGrid.respondsTo, lineageGrid.grade)

def theravadaStageTag (_p : Unit) : LineageStage :=
  LineageStage.theravada Path.onceReturn

def bullsStageTag (_p : Unit) : LineageStage :=
  LineageStage.bulls Grid.BullStage.taming

theorem no_lineage_stage_recovery :
    ¬ ∃ recover : LineageSeenData → Unit → LineageStage,
        recover lineageSeenData = theravadaStageTag ∧
        recover lineageSeenData = bullsStageTag := by
  rintro ⟨recover, htheravada, hbulls⟩
  have htheravadaTag :
      recover lineageSeenData () =
        LineageStage.theravada Path.onceReturn := by
    rw [htheravada]
    rfl
  have hbullsTag :
      recover lineageSeenData () =
        LineageStage.bulls Grid.BullStage.taming := by
    rw [hbulls]
    rfl
  rw [htheravadaTag] at hbullsTag
  cases hbullsTag

/-- Specializing `CorrelationsNegative.no_stage_boundary_recovery`: the same
    grid and run can be re-diagnosed under a Theravada-shaped factor tag or a
    Bulls-shaped tag. Switching lineage changes the supplied reading in force,
    not the welds seen by the grid. -/
theorem lineage_underdetermined_by_seen_run :
    lineageRun = [lineageWeld] ∧
      theravadaFactorScheme.proj () =
        LineageStage.theravada Path.onceReturn ∧
      bullsLineageScheme.proj () =
        LineageStage.bulls Grid.BullStage.taming ∧
      theravadaFactorScheme.proj () ≠ bullsLineageScheme.proj () ∧
      ¬ ∃ recover : LineageSeenData → Unit → LineageStage,
        recover lineageSeenData = theravadaStageTag ∧
          recover lineageSeenData = bullsStageTag := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · intro h
          cases h
        · exact no_lineage_stage_recovery

end FactorsNegative

end WAA
