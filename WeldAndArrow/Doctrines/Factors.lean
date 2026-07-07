/-
================================================================================
  WeldAndArrow.Doctrines.Factors
  Path-factor hold/release readings over the fetter table
================================================================================
-/

import WeldAndArrow.Doctrines.Fetters
import WeldAndArrow.Doctrines.SuddenGradual

namespace WAA

/- ==============================================================================
   Factor data and derived classes
============================================================================== -/

inductive PathFactor
  | rites
  | view
  | resolve
  | speech
  | conduct

namespace PathFactor

/-- Factor blocker classes are derived from the supplied fetter reading. The
    first stream-entry pair covers rites-grasp plus the blockers of right view;
    speech and conduct are named but intentionally inert in this phase. -/
def blockerClass {Contrib : Type} [PreorderBot Contrib] {G : Grid Contrib}
    (fr : G.FetterReading) : PathFactor → G.Call → Prop
  | .rites, c => fr.provocationClass Fetter.ritesGrasp c
  | .view, c =>
      fr.provocationClass Fetter.identityView c ∨
        fr.provocationClass Fetter.doubt c
  | .resolve, c =>
      fr.provocationClass Fetter.sensualDesire c ∨
        fr.provocationClass Fetter.illWill c
  | .speech, _ => False
  | .conduct, _ => False

end PathFactor

namespace Grid

open DirectedConvention
open DirectedConvention.BeingConvention

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

theorem ritesView_union_covers_streamEntry_fetters
    (fr : G.FetterReading) (c : G.Call) :
    (PathFactor.blockerClass fr PathFactor.rites c ∨
      PathFactor.blockerClass fr PathFactor.view c) ↔
      Path.cutClasses fr Path.streamEntry c := by
  constructor
  · intro h
    rcases h with hrites | hview
    · exact ⟨Fetter.ritesGrasp, rfl, hrites⟩
    · rcases hview with hidentity | hdoubt
      · exact ⟨Fetter.identityView, rfl, hidentity⟩
      · exact ⟨Fetter.doubt, rfl, hdoubt⟩
  · rintro ⟨f, hf, hclass⟩
    cases f with
    | identityView => exact Or.inr (Or.inl hclass)
    | doubt => exact Or.inr (Or.inr hclass)
    | ritesGrasp => exact Or.inl hclass
    | sensualDesire => cases hf
    | illWill => cases hf
    | formDesire => cases hf
    | formlessDesire => cases hf
    | conceit => cases hf
    | restlessness => cases hf
    | ignorance => cases hf

theorem resolve_covers_nonReturn_fetters
    (fr : G.FetterReading) (c : G.Call) :
    PathFactor.blockerClass fr PathFactor.resolve c ↔
      ∃ f : Fetter,
        Fetter.abandonedAt f = Path.nonReturn ∧ fr.provocationClass f c := by
  constructor
  · intro h
    rcases h with hsensual | hill
    · exact ⟨Fetter.sensualDesire, rfl, hsensual⟩
    · exact ⟨Fetter.illWill, rfl, hill⟩
  · rintro ⟨f, hf, hclass⟩
    cases f with
    | identityView => cases hf
    | doubt => cases hf
    | ritesGrasp => cases hf
    | sensualDesire => exact Or.inl hclass
    | illWill => exact Or.inr hclass
    | formDesire => cases hf
    | formlessDesire => cases hf
    | conceit => cases hf
    | restlessness => cases hf
    | ignorance => cases hf

/-- The three active factor blocker classes cover exactly the lower-fetter
    provocation classes. This extends the table-coherence anchor
    `Fetter.kind_lower_iff_cut_by_nonReturn`: the lower fetters are precisely
    those cut by non-return, now regrouped as rites, view, and resolve. -/
theorem lower_fetters_covered_by_rites_view_resolve
    (fr : G.FetterReading) (c : G.Call) :
    (PathFactor.blockerClass fr PathFactor.rites c ∨
      PathFactor.blockerClass fr PathFactor.view c ∨
        PathFactor.blockerClass fr PathFactor.resolve c) ↔
      Path.cutClasses fr Path.nonReturn c := by
  constructor
  · intro h
    rcases h with hrites | hview | hresolve
    · exact ⟨Fetter.ritesGrasp, Or.inl rfl, hrites⟩
    · rcases hview with hidentity | hdoubt
      · exact ⟨Fetter.identityView, Or.inl rfl, hidentity⟩
      · exact ⟨Fetter.doubt, Or.inl rfl, hdoubt⟩
    · rcases hresolve with hsensual | hill
      · exact ⟨Fetter.sensualDesire, Or.inr rfl, hsensual⟩
      · exact ⟨Fetter.illWill, Or.inr rfl, hill⟩
  · rintro ⟨f, hf, hclass⟩
    cases f with
    | identityView => exact Or.inr (Or.inl (Or.inl hclass))
    | doubt => exact Or.inr (Or.inl (Or.inr hclass))
    | ritesGrasp => exact Or.inl hclass
    | sensualDesire => exact Or.inr (Or.inr (Or.inl hclass))
    | illWill => exact Or.inr (Or.inr (Or.inr hclass))
    | formDesire =>
        rcases hf with h | h <;> cases h
    | formlessDesire =>
        rcases hf with h | h <;> cases h
    | conceit =>
        rcases hf with h | h <;> cases h
    | restlessness =>
        rcases hf with h | h <;> cases h
    | ignorance =>
        rcases hf with h | h <;> cases h

/- ==============================================================================
   Hold / Release
============================================================================== -/

/-- A factor is HELD when a live self-pole weld in its blocker class is
    witnessed in the seen run. Hold is not an error: a stage-appropriate hold
    can be correct. The Hold/Release pair lives on the agent-factor frame,
    unlike freeze/collapse on the utterance/distinction frame and unlike
    clench/quietness on the share frame. -/
def FactorHeld {Macro : Type} (κ : BeingCoarsening G Macro) (b : Macro)
    (fr : G.FetterReading) (φ : PathFactor) (run : List G.Weld) : Prop :=
  ∃ w ∈ run, G.Actual w ∧ κ.InFiber b w ∧
    PathFactor.blockerClass fr φ w.call ∧ G.HasSelfPoleIndex w

/-- A factor is RELEASED when the fiber is at pole on its blocker class. This
    is a whole-class cut, so one actual in-fiber live weld in the class refutes
    it. -/
def FactorReleased {Macro : Type} (κ : BeingCoarsening G Macro) (b : Macro)
    (fr : G.FetterReading) (φ : PathFactor) : Prop :=
  κ.FiberAtPoleOn b (PathFactor.blockerClass fr φ)

theorem not_factorHeld_of_factorReleased {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {fr : G.FetterReading} {φ : PathFactor} {run : List G.Weld}
    (h : G.FactorReleased κ b fr φ) :
    ¬ G.FactorHeld κ b fr φ run := by
  rintro ⟨w, _hmem, hactual, hfiber, hclass, hidx⟩
  exact (κ.no_live_index_under_fiberAtPoleOn h hactual hfiber hclass) hidx

theorem factorReleased_rites_iff_ritesGrasp_cut {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Macro) (fr : G.FetterReading) :
    G.FactorReleased κ b fr PathFactor.rites ↔
      G.FetterCut κ b fr Fetter.ritesGrasp :=
  Iff.rfl

theorem factorReleased_view_iff {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Macro) (fr : G.FetterReading) :
    G.FactorReleased κ b fr PathFactor.view ↔
      G.FetterCut κ b fr Fetter.identityView ∧
        G.FetterCut κ b fr Fetter.doubt := by
  constructor
  · intro h
    constructor
    · intro w hactual hfiber hclass
      exact h w hactual hfiber (Or.inl hclass)
    · intro w hactual hfiber hclass
      exact h w hactual hfiber (Or.inr hclass)
  · rintro ⟨hidentity, hdoubt⟩ w hactual hfiber hclass
    rcases hclass with hclass | hclass
    · exact hidentity w hactual hfiber hclass
    · exact hdoubt w hactual hfiber hclass

theorem factorReleased_resolve_iff {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Macro) (fr : G.FetterReading) :
    G.FactorReleased κ b fr PathFactor.resolve ↔
      G.FetterCut κ b fr Fetter.sensualDesire ∧
        G.FetterCut κ b fr Fetter.illWill := by
  constructor
  · intro h
    constructor
    · intro w hactual hfiber hclass
      exact h w hactual hfiber (Or.inl hclass)
    · intro w hactual hfiber hclass
      exact h w hactual hfiber (Or.inr hclass)
  · rintro ⟨hsensual, hill⟩ w hactual hfiber hclass
    rcases hclass with hclass | hclass
    · exact hsensual w hactual hfiber hclass
    · exact hill w hactual hfiber hclass

/- ==============================================================================
   Stage readings
============================================================================== -/

def WaaStreamEnterer {Macro : Type} (κ : BeingCoarsening G Macro)
    (b : Macro) (fr : G.FetterReading) (run : List G.Weld) : Prop :=
  G.FactorReleased κ b fr PathFactor.rites ∧
    G.FactorHeld κ b fr PathFactor.view run

def WaaStreamWinner {Macro : Type} (κ : BeingCoarsening G Macro)
    (b : Macro) (fr : G.FetterReading) : Prop :=
  G.FactorReleased κ b fr PathFactor.rites ∧
    G.FactorReleased κ b fr PathFactor.view

def WaaOnceReturner {Macro : Type} (κ : BeingCoarsening G Macro)
    (b : Macro) (fr : G.FetterReading) (run : List G.Weld) : Prop :=
  G.WaaStreamWinner κ b fr ∧
    G.FactorHeld κ b fr PathFactor.resolve run

def WaaNonReturner {Macro : Type} (κ : BeingCoarsening G Macro)
    (b : Macro) (fr : G.FetterReading) : Prop :=
  G.WaaStreamWinner κ b fr ∧
    G.FactorReleased κ b fr PathFactor.resolve

/- The upper-half pair is deliberately named and inert in this phase.

   `PathFactor.speech` and `PathFactor.conduct` currently have `False`
   blocker classes. The open question is what "holding a factor" should mean
   in grid terms when the arhat is at `FiberAtPole`: `FactorHeld` requires
   `HasSelfPoleIndex`, while the existing arhat anchors refute live indexes
   fiber-wide. The reserved prose name `Seclusion` belongs to the future
   speech-release stage's held factor; no declaration is introduced yet.
-/

theorem waaStreamWinner_iff_streamEntry_cutClasses {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Macro) (fr : G.FetterReading) :
    G.WaaStreamWinner κ b fr ↔
      κ.FiberAtPoleOn b (Path.cutClasses fr Path.streamEntry) := by
  constructor
  · rintro ⟨hrites, hview⟩ w hactual hfiber hclass
    have hcovered :
        PathFactor.blockerClass fr PathFactor.rites w.call ∨
          PathFactor.blockerClass fr PathFactor.view w.call :=
      (G.ritesView_union_covers_streamEntry_fetters fr w.call).mpr hclass
    rcases hcovered with hcovered | hcovered
    · exact hrites w hactual hfiber hcovered
    · exact hview w hactual hfiber hcovered
  · intro hcut
    constructor
    · intro w hactual hfiber hclass
      exact hcut w hactual hfiber
        ((G.ritesView_union_covers_streamEntry_fetters fr w.call).mp
          (Or.inl hclass))
    · intro w hactual hfiber hclass
      exact hcut w hactual hfiber
        ((G.ritesView_union_covers_streamEntry_fetters fr w.call).mp
          (Or.inr hclass))

theorem waaNonReturner_iff_nonReturn_cut {Macro : Type}
    (κ : BeingCoarsening G Macro) (b : Macro) (fr : G.FetterReading) :
    G.WaaNonReturner κ b fr ↔
      κ.FiberAtPoleOn b (Path.cutClasses fr Path.nonReturn) := by
  constructor
  · rintro ⟨hstream, hresolve⟩ w hactual hfiber hclass
    have hcovered :
        PathFactor.blockerClass fr PathFactor.rites w.call ∨
          PathFactor.blockerClass fr PathFactor.view w.call ∨
            PathFactor.blockerClass fr PathFactor.resolve w.call :=
      (G.lower_fetters_covered_by_rites_view_resolve fr w.call).mpr hclass
    rcases hcovered with hrites | hview | hresolveClass
    · exact hstream.left w hactual hfiber hrites
    · exact hstream.right w hactual hfiber hview
    · exact hresolve w hactual hfiber hresolveClass
  · intro hcut
    constructor
    · constructor
      · intro w hactual hfiber hclass
        exact hcut w hactual hfiber
          ((G.lower_fetters_covered_by_rites_view_resolve fr w.call).mp
            (Or.inl hclass))
      · intro w hactual hfiber hclass
        exact hcut w hactual hfiber
          ((G.lower_fetters_covered_by_rites_view_resolve fr w.call).mp
            (Or.inr (Or.inl hclass)))
    · intro w hactual hfiber hclass
      exact hcut w hactual hfiber
        ((G.lower_fetters_covered_by_rites_view_resolve fr w.call).mp
          (Or.inr (Or.inr hclass)))

theorem waaNonReturner_of_arhatFiber
    {κ : G.PathScheme} (fr : G.FetterReading)
    (h : κ.FiberAtPole Path.arhatship) :
    G.WaaNonReturner κ Path.arhatship fr := by
  apply (G.waaNonReturner_iff_nonReturn_cut κ Path.arhatship fr).mpr
  intro w hactual hfiber _hclass
  exact h w hactual hfiber

theorem waaStreamWinner_of_waaNonReturner {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro} {fr : G.FetterReading}
    (h : G.WaaNonReturner κ b fr) :
    G.WaaStreamWinner κ b fr :=
  h.left

theorem not_waaStreamEnterer_view_hold_of_waaStreamWinner {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {fr : G.FetterReading} {run : List G.Weld}
    (h : G.WaaStreamWinner κ b fr) :
    ¬ G.FactorHeld κ b fr PathFactor.view run :=
  G.not_factorHeld_of_factorReleased h.right

theorem not_waaStreamEnterer_of_waaStreamWinner {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {fr : G.FetterReading} {run : List G.Weld}
    (h : G.WaaStreamWinner κ b fr) :
    ¬ G.WaaStreamEnterer κ b fr run := by
  intro henterer
  exact G.not_waaStreamEnterer_view_hold_of_waaStreamWinner h henterer.right

/- ==============================================================================
   Once-return attenuation
============================================================================== -/

/-- A share-drop run restricted to one supplied call-class. -/
def ShareDropRunOn (before : Config Contrib) (cs : G.Call → Prop)
    (run : List G.Weld) : Prop :=
  G.ShareDropRun before run ∧ ∀ w : G.Weld, w ∈ run → cs w.call

theorem shareDropRunOn_univ_iff_shareDropRun
    (before : Config Contrib) (run : List G.Weld) :
    G.ShareDropRunOn before (fun _ => True) run ↔
      G.ShareDropRun before run := by
  constructor
  · intro h
    exact h.left
  · intro h
    exact ⟨h, fun _w _hmem => True.intro⟩

def ShareDropRunOnFactor (fr : G.FetterReading) (φ : PathFactor)
    (run : List G.Weld) : Prop :=
  ∃ before : Config Contrib,
    G.ShareDropRunOn before (PathFactor.blockerClass fr φ) run

/-- Once-return attenuation is a real resolve-class share-drop run whose final
    tendency has not yet reached the pole. It gives once-return positive
    checked content without adding a new cut class. -/
def WaaResolveAttenuation {Macro : Type} (_κ : BeingCoarsening G Macro)
    (_b : Macro) (fr : G.FetterReading) (run : List G.Weld) : Prop :=
  ∃ (before : Config Contrib) (received : G.Weld) (rest : List G.Weld),
    run = received :: rest ∧
      G.ShareDropRunOn before (PathFactor.blockerClass fr PathFactor.resolve)
        run ∧
      ¬ AtBot before.tendency ∧
      ¬ AtBot ((G.rePitchRun before run).tendency)

def registerResolveFactorReading : registerClockGrid.FetterReading where
  provocationClass
    | Fetter.sensualDesire, _ => True
    | _, _ => False

def registerResolveWeld : registerClockGrid.Weld :=
  ⟨(2 : Nat), (), (3 : Nat)⟩

def registerResolveRun : List registerClockGrid.Weld :=
  [registerResolveWeld]

theorem registerResolve_streamWinner :
    registerClockGrid.WaaStreamWinner registerClockCoarsening ()
      registerResolveFactorReading := by
  constructor
  · intro _w _hactual _hfiber hclass
    cases hclass
  · intro _w _hactual _hfiber hclass
    rcases hclass with hclass | hclass <;> cases hclass

theorem registerResolve_held :
    registerClockGrid.FactorHeld registerClockCoarsening ()
      registerResolveFactorReading PathFactor.resolve registerResolveRun := by
  refine ⟨registerResolveWeld, ?_, rfl, rfl, ?_, ?_⟩
  · simp [registerResolveRun]
  · exact Or.inl True.intro
  · dsimp [Grid.HasSelfPoleIndex, Grid.share, registerClockGrid,
      registerResolveWeld, AtBot, shareBot]
    change ¬ (2 : Nat) ≤ 0
    exact Nat.not_succ_le_zero 1

theorem registerResolve_attenuation :
    registerClockGrid.WaaResolveAttenuation registerClockCoarsening ()
      registerResolveFactorReading registerResolveRun := by
  refine ⟨{ tendency := 5 }, registerResolveWeld, [], rfl, ?_, ?_, ?_⟩
  · constructor
    · refine Grid.ShareDropRun.cons ?_ ?_ ?_
      · rfl
      · dsimp [Grid.IsShareDrop, Grid.share, registerClockGrid,
          registerResolveWeld]
        constructor
        · change (2 : Nat) ≤ 5
          decide
        · change ¬ (5 : Nat) ≤ 2
          decide
      · exact Grid.ShareDropRun.nil _
    · intro w hmem
      simp [registerResolveRun] at hmem
      subst w
      exact Or.inl True.intro
  · dsimp [AtBot, shareBot]
    change ¬ (5 : Nat) ≤ 0
    exact Nat.not_succ_le_zero 4
  · dsimp [Grid.rePitchRun, Grid.rePitch, Grid.share, registerClockGrid,
      registerResolveRun, registerResolveWeld, AtBot, shareBot]
    change ¬ (2 : Nat) ≤ 0
    exact Nat.not_succ_le_zero 1

theorem registerResolve_not_released :
    ¬ registerClockGrid.FactorReleased registerClockCoarsening ()
      registerResolveFactorReading PathFactor.resolve := by
  intro hrelease
  have hbot : AtBot (registerClockGrid.share registerResolveWeld) :=
    hrelease registerResolveWeld rfl rfl (Or.inl True.intro)
  dsimp [Grid.share, registerClockGrid, registerResolveWeld, AtBot, shareBot]
    at hbot
  change (2 : Nat) ≤ 0 at hbot
  exact Nat.not_succ_le_zero 1 hbot

theorem waaOnceReturner_attenuation_witness :
    ∃ (fr : registerClockGrid.FetterReading)
      (run : List registerClockGrid.Weld),
      registerClockGrid.WaaOnceReturner registerClockCoarsening () fr run ∧
        registerClockGrid.WaaResolveAttenuation registerClockCoarsening ()
          fr run ∧
        ¬ registerClockGrid.FactorReleased registerClockCoarsening ()
          fr PathFactor.resolve := by
  refine ⟨registerResolveFactorReading, registerResolveRun, ?_,
    registerResolve_attenuation, registerResolve_not_released⟩
  exact ⟨registerResolve_streamWinner, registerResolve_held⟩

theorem attenuation_not_release :
    ∃ (fr : registerClockGrid.FetterReading)
      (run : List registerClockGrid.Weld),
      registerClockGrid.WaaResolveAttenuation registerClockCoarsening ()
        fr run ∧
        ¬ registerClockGrid.FactorReleased registerClockCoarsening ()
          fr PathFactor.resolve := by
  rcases waaOnceReturner_attenuation_witness with
    ⟨fr, run, _honce, hatt, hnotRelease⟩
  exact ⟨fr, run, hatt, hnotRelease⟩

/- ==============================================================================
   Serial factor regime
============================================================================== -/

def RunsExhibitFactorOrder (fr : G.FetterReading)
    (runs : List (List G.Weld)) : Prop :=
  ∃ ritesRun viewRun resolveRun : List G.Weld,
    runs = [ritesRun, viewRun, resolveRun] ∧
      G.ShareDropRunOnFactor fr PathFactor.rites ritesRun ∧
      G.ShareDropRunOnFactor fr PathFactor.view viewRun ∧
      G.ShareDropRunOnFactor fr PathFactor.resolve resolveRun

/-- The serial-factor regime is the conditional voice for "usually runs in
    order": if the seen runs exhibit share-drops in the derived factor order
    rites-before-view-before-resolve, the supplied regime promotes the path
    readings to their corresponding fruit readings along those runs. The grid
    does not discharge the antecedent. The guards are
    `WaaSuddenArrival` and
    `SuddenGradualNegative.subitism_frequency_underdetermined`; no frequency
    claim is introduced, only ordering inside this regime. -/
def WaaSerialFactorRegime {Macro : Type} (κ : BeingCoarsening G Macro)
    (b : Macro) (fr : G.FetterReading)
    (runs : List (List G.Weld)) : Prop :=
  G.RunsExhibitFactorOrder fr runs →
    (∀ run ∈ runs,
      G.WaaStreamEnterer κ b fr run → G.WaaStreamWinner κ b fr) ∧
    (∀ run ∈ runs,
      G.WaaOnceReturner κ b fr run → G.WaaNonReturner κ b fr)

theorem waaSerialFactorRegime_conditional {Macro : Type}
    {κ : BeingCoarsening G Macro} {b : Macro}
    {fr : G.FetterReading} {runs : List (List G.Weld)}
    (hregime : G.WaaSerialFactorRegime κ b fr runs)
    (horder : G.RunsExhibitFactorOrder fr runs) :
    (∀ run ∈ runs,
      G.WaaStreamEnterer κ b fr run → G.WaaStreamWinner κ b fr) ∧
    (∀ run ∈ runs,
      G.WaaOnceReturner κ b fr run → G.WaaNonReturner κ b fr) :=
  hregime horder

theorem waaSuddenArrival_consistent_with_factorScheme
    {κ : G.PathScheme} {before : Config Contrib} {received : G.Weld}
    (fr : G.FetterReading)
    (hsudden : G.WaaSuddenArrival before received)
    (hfiber : κ.FiberAtPole Path.arhatship) :
    G.WaaSuddenArrival before received ∧
      G.WaaStreamWinner κ Path.arhatship fr ∧
        G.WaaNonReturner κ Path.arhatship fr := by
  have hnonReturner : G.WaaNonReturner κ Path.arhatship fr :=
    G.waaNonReturner_of_arhatFiber fr hfiber
  exact ⟨hsudden, hnonReturner.left, hnonReturner⟩

end Grid

end WAA
