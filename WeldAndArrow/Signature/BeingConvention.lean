/-
================================================================================
  WeldAndArrow.Signature.BeingConvention
  Being-convention vocabulary and diagnosis-time coarsenings
================================================================================

Reading and motivation: Identification/Commentary.lean, C.1.
-/

import WeldAndArrow.Signature.Grid

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

namespace DirectedConvention
namespace BeingConvention

/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
abbrev MountsAt (b : G.Being) (c : G.Call) : Prop := G.MountsAt b c

/-- Re-rooted name for mounting at some call. -/
abbrev MountsSomewhere (b : G.Being) : Prop := G.MountsSomewhere b

/-- Re-rooted name for call-entire response. -/
abbrev RespondsToEveryCall (b : G.Being) : Prop := G.RespondsToEveryCall b

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
abbrev Stone (b : G.Being) : Prop := G.Stone b

/-- Re-rooted name for the pole-class responder. -/
abbrev Terminus (b : G.Being) : Prop := G.Terminus b

/-- Re-rooted name for non-vacuous terminus response. -/
abbrev LiveTerminus (b : G.Being) : Prop := G.LiveTerminus b

/-- Re-rooted name for call-entire terminus response. -/
abbrev ResponsiveTerminus (b : G.Being) : Prop := G.ResponsiveTerminus b

/-- Re-rooted name for the two attested arrivals at the pole-class. -/
abbrev AtPoleClass (b : G.Being) : Prop := G.AtPoleClass b

/-- Re-rooted name for the probe, because the probe reads a being's
    composition rather than adding a field to the signature. -/
abbrev ProbeConstant (b : G.Being) (cs : G.Call → Prop) : Prop :=
  G.ProbeConstant b cs

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
structure BeingCoarsening (G : Grid Contrib) (Macro : Type) where
  proj : G.Being → Macro

namespace BeingCoarsening

variable {G : Grid Contrib} {Macro : Type} (κ : BeingCoarsening G Macro)

/-- A weld lies in a macro tag's fiber when its fine agent projects there. -/
def InFiber (b : Macro) (w : G.Weld) : Prop := κ.proj w.agent = b

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def SameFiber (p q : G.Being) : Prop := κ.proj p = κ.proj q

/-- A fiber has at least one fine tag under it. -/
def FiberInhabited (b : Macro) : Prop := ∃ p : G.Being, κ.proj p = b

/-- A fiber has at least one actual weld under it. This is the live/vacuity
    guard needed for exclusivity facts below. -/
def ActualFiberInhabited (b : Macro) : Prop :=
  ∃ w : G.Weld, G.Actual w ∧ κ.InFiber b w

/-- Some fine tag in the fiber mounts a response somewhere. -/
def SentientTag (b : Macro) : Prop :=
  ∃ p : G.Being, κ.proj p = b ∧ G.MountsSomewhere p

/-- A tag is not sentient exactly when every fine tag in its fiber is stone-typed. -/
theorem not_sentientTag_iff_fiber_all_stone (b : Macro) :
    ¬ κ.SentientTag b ↔ ∀ p : G.Being, κ.proj p = b → G.Stone p := by
  constructor
  · intro hnot p hp c hmount
    exact hnot ⟨p, hp, ⟨c, hmount⟩⟩
  · intro hall hsent
    rcases hsent with ⟨p, hp, c, hmount⟩
    exact hall p hp c hmount

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def FiberAtPole (b : Macro) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w → AtBot (G.share w)

/-- The live, non-vacuous fiber-at-pole predicate. -/
def LiveFiberAtPole (b : Macro) : Prop :=
  κ.ActualFiberInhabited b ∧ κ.FiberAtPole b

/-- A fiber reads at the pole on a supplied call-class. This is neutral fiber
    vocabulary: downstream doctrines supply the class predicate. -/
def FiberAtPoleOn (b : Macro) (cs : G.Call → Prop) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w → cs w.call → AtBot (G.share w)

/-- A fiber has an actual weld in the supplied call-class. -/
def ActualFiberInhabitedOn (b : Macro) (cs : G.Call → Prop) : Prop :=
  ∃ w : G.Weld, G.Actual w ∧ κ.InFiber b w ∧ cs w.call

/-- The live, non-vacuous class-restricted fiber-at-pole predicate. -/
def LiveFiberAtPoleOn (b : Macro) (cs : G.Call → Prop) : Prop :=
  κ.ActualFiberInhabitedOn b cs ∧ κ.FiberAtPoleOn b cs

/-- Every actual weld in the fiber carries a live self-pole index.
    Vacuous on empty or no-actual fibers; use `LiveSelfAptTag` when
    inhabitation matters. -/
def SelfAptTag (b : Macro) : Prop :=
  ∀ w : G.Weld, G.Actual w → κ.InFiber b w → G.HasSelfPoleIndex w

/-- The live, non-vacuous self-apt predicate. -/
def LiveSelfAptTag (b : Macro) : Prop :=
  κ.ActualFiberInhabited b ∧ κ.SelfAptTag b

/-- Patchy fiber: neither all actual welds are at the pole nor all actual
    welds are self-apt. No middling scalar is smuggled in. -/
def Patchy (b : Macro) : Prop := ¬ κ.FiberAtPole b ∧ ¬ κ.SelfAptTag b

/-- If every fine tag in the fiber is terminus-typed, the whole actual fiber
    reads at the pole. -/
theorem fiberAtPole_of_fiber_termini {b : Macro}
    (h : ∀ p : G.Being, κ.proj p = b → G.Terminus p) :
    κ.FiberAtPole b := by
  intro w hactual hfiber
  exact G.atBot_of_terminus_response (h w.agent hfiber) hactual

/-- Under a fiber-at-pole reading, no actual weld in the fiber has a live
    self-pole index. -/
theorem no_live_index_under_fiberAtPole {b : Macro}
    (h : κ.FiberAtPole b) {w : G.Weld}
    (hactual : G.Actual w) (hfiber : κ.InFiber b w) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_atBot w (h w hactual hfiber)

theorem fiberAtPoleOn_mono {b : Macro} {cs ds : G.Call → Prop}
    (h : κ.FiberAtPoleOn b cs)
    (hsub : ∀ c : G.Call, ds c → cs c) :
    κ.FiberAtPoleOn b ds :=
  fun w hactual hfiber hds => h w hactual hfiber (hsub w.call hds)

theorem fiberAtPoleOn_univ_iff (b : Macro) :
    κ.FiberAtPoleOn b (fun _ => True) ↔ κ.FiberAtPole b := by
  constructor
  · intro h w hactual hfiber
    exact h w hactual hfiber True.intro
  · intro h w hactual hfiber _hclass
    exact h w hactual hfiber

theorem no_live_index_under_fiberAtPoleOn {b : Macro} {cs : G.Call → Prop}
    (h : κ.FiberAtPoleOn b cs) {w : G.Weld}
    (hactual : G.Actual w) (hfiber : κ.InFiber b w) (hclass : cs w.call) :
    ¬ G.HasSelfPoleIndex w :=
  G.no_self_pole_index_of_atBot w (h w hactual hfiber hclass)

/-- Fiber soul-guard: even where the self-convention is apt, the index is
    only the per-weld agent tag. No macro owner is produced. -/
theorem selfAptTag_indices_are_per_weld_only {b : Macro}
    (h : κ.SelfAptTag b) {w : G.Weld}
    (hactual : G.Actual w) (hfiber : κ.InFiber b w) :
    G.selfPoleIndex w (h w hactual hfiber) = w.agent :=
  rfl

/-- The empty-fiber vacuity guard: fiber-at-pole and self-apt are exclusive
    only once an actual weld in the fiber is supplied. -/
theorem fiberAtPole_selfAptTag_exclusive {b : Macro}
    (hinh : κ.ActualFiberInhabited b)
    (hpole : κ.FiberAtPole b) (hself : κ.SelfAptTag b) :
    False := by
  rcases hinh with ⟨w, hactual, hfiber⟩
  exact hself w hactual hfiber (hpole w hactual hfiber)

theorem liveFiberAtPole_not_selfAptTag {b : Macro}
    (h : κ.LiveFiberAtPole b) :
    ¬ κ.SelfAptTag b :=
  fun hself => κ.fiberAtPole_selfAptTag_exclusive h.left h.right hself

theorem liveSelfAptTag_not_fiberAtPole {b : Macro}
    (h : κ.LiveSelfAptTag b) :
    ¬ κ.FiberAtPole b :=
  fun hpole => κ.fiberAtPole_selfAptTag_exclusive h.left hpole h.right

/-- Internal refinement within sentience: the fiber carries at least one
    internal delivery line. Any persistence theorem built from this owes a
    model-supplied asymmetry or irreflexivity hypothesis on `conditions`. -/
def SelfConditioningTag (b : Macro) : Prop :=
  ∃ deed reception : G.Weld,
    κ.InFiber b deed ∧ κ.InFiber b reception ∧
    G.Actual reception ∧ DeliveredTo G deed reception

/-- A stronger asymptote: every actual reception in the fiber is internally
    fed. It is named and shelved because treating it as the default would
    turn internal conditioning into causal solipsism. -/
def StrongSelfConditioningTag (b : Macro) : Prop :=
  ∀ reception : G.Weld, κ.InFiber b reception → G.Actual reception →
    ∃ deed : G.Weld, κ.InFiber b deed ∧ DeliveredTo G deed reception

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
structure Delegation (b : Macro) where
  weld : G.Weld
  actual : G.Actual weld
  delegate_in_fiber : κ.InFiber b weld

namespace Delegation

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def share {b : Macro} (d : κ.Delegation b) : Contrib := G.share d.weld

@[simp]
theorem share_eq_delegate_share {b : Macro} (d : κ.Delegation b) :
    d.share = G.share d.weld :=
  rfl

end Delegation

/-- Transpose a being-coarsening across the condition-transpose operation.
    Fine tags are unchanged; only delivery order reverses. -/
def transpose (κ : BeingCoarsening G Macro) :
    BeingCoarsening G.transpose Macro where
  proj := κ.proj

theorem transpose_inFiber_iff
    (κ : BeingCoarsening G Macro) (b : Macro) (w : G.Weld) :
    κ.transpose.InFiber b w ↔ κ.InFiber b w :=
  Iff.rfl

theorem transpose_sentientTag_iff
    (κ : BeingCoarsening G Macro) (b : Macro) :
    κ.transpose.SentientTag b ↔ κ.SentientTag b :=
  Iff.rfl

/-- Direction-smuggling detector for the directed refinement: transposition
    reverses the delivery line while leaving fiber membership and actuality
    untouched. -/
theorem transpose_selfConditioningTag
    (κ : BeingCoarsening G Macro) (b : Macro) :
    κ.transpose.SelfConditioningTag b ↔
      ∃ deed reception : G.Weld,
        κ.InFiber b deed ∧ κ.InFiber b reception ∧
        G.Actual reception ∧ DeliveredTo G reception deed := by
  constructor
  · rintro ⟨deed, reception, hdeed, hreception, hactual, hdel⟩
    exact ⟨deed, reception, hdeed, hreception, hactual,
      (DirectedConvention.transpose_deliveredTo_iff G deed reception).mp hdel⟩
  · rintro ⟨deed, reception, hdeed, hreception, hactual, hdel⟩
    exact ⟨deed, reception, hdeed, hreception, hactual,
      (DirectedConvention.transpose_deliveredTo_iff G deed reception).mpr hdel⟩

end BeingCoarsening

/- The innermost `GridConvention` namespace is opened in the Consequences
   files for the concrete claim-language rows. Keeping the abstract machinery
   at `Grid` level for now avoids a churn-only migration of structure fields
   whose eventual home may simply remain signature rather than reading. -/

end BeingConvention

end DirectedConvention

end Grid

end WAA
