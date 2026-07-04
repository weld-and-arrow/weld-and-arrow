/-
================================================================================
  The Weld and the Arrow — IV. Invariance
  Display reparameterization for the contribution carrier
================================================================================

This file is the admission criterion for future grade-facing predicates:
anything that depends on `Contrib` owes a transport lemma here, or it is
operational residue by definition. The theorems below are the formal content
of treating contribution values as display conventions over the preorder.
-/

import WeldAndArrow.Identification

namespace WAA

/-- A display-reparameterization: preserves and reflects the ordering and the
    pole-class. The invariance theorems below are the formal content of
    "display conventions over that partial order". -/
structure DisplayReparam (Contrib Contrib' : Type)
    [PreorderBot Contrib] [PreorderBot Contrib'] where
  toFun     : Contrib → Contrib'
  le_iff    : ∀ a b, a ≼ b ↔ toFun a ≼ toFun b
  atBot_bot : AtBot (toFun shareZero)

namespace DisplayReparam

variable {Contrib Contrib' : Type} [PreorderBot Contrib] [PreorderBot Contrib']
variable (f : DisplayReparam Contrib Contrib')

/-- Reparameterization preserves and reflects the pole-class. -/
theorem atBot_iff (a : Contrib) :
    AtBot (f.toFun a) ↔ AtBot a := by
  constructor
  · intro h
    exact (f.le_iff a shareZero).mpr
      (Preorder.le_trans h (shareZero_le (f.toFun shareZero)))
  · intro h
    exact Preorder.le_trans ((f.le_iff a shareZero).mp h) f.atBot_bot

/-- Reparameterization preserves and reflects order-equivalence. -/
theorem orderEq_iff (a b : Contrib) :
    OrderEq (f.toFun a) (f.toFun b) ↔ OrderEq a b := by
  constructor
  · intro h
    exact ⟨(f.le_iff a b).mpr h.left, (f.le_iff b a).mpr h.right⟩
  · intro h
    exact ⟨(f.le_iff a b).mp h.left, (f.le_iff b a).mp h.right⟩

end DisplayReparam

namespace Config

variable {Contrib Contrib' : Type} [PreorderBot Contrib] [PreorderBot Contrib']

/-- Transport a stored display tendency along a display reparameterization. -/
def map (before : Config Contrib) (f : DisplayReparam Contrib Contrib') :
    Config Contrib' :=
  { tendency := f.toFun before.tendency }

theorem map_tendency (before : Config Contrib)
    (f : DisplayReparam Contrib Contrib') :
    (before.map f).tendency = f.toFun before.tendency :=
  rfl

end Config

namespace Grid

variable {Contrib Contrib' : Type} [PreorderBot Contrib] [PreorderBot Contrib']

/-- Transport a grid by reparameterizing only its Row-2 display carrier. -/
def map (G : Grid Contrib) (f : DisplayReparam Contrib Contrib') :
    Grid Contrib' where
  Being      := G.Being
  Call       := G.Call
  Response   := G.Response
  respondsTo := G.respondsTo
  grade      := fun b c r => f.toFun (G.grade b c r)
  conditions := G.conditions

variable (G : Grid Contrib) (f : DisplayReparam Contrib Contrib')

theorem map_grade (b : G.Being) (c : G.Call) (r : G.Response) :
    (G.map f).grade b c r = f.toFun (G.grade b c r) :=
  rfl

theorem map_share (w : G.Weld) :
    (G.map f).share w = f.toFun (G.share w) :=
  rfl

/-- Function-side predicates do not mention the contribution carrier, so they
    transport by definitional unfolding. -/
theorem map_actual_iff (w : G.Weld) :
    (G.map f).Actual w ↔ G.Actual w :=
  Iff.rfl

theorem map_mountsAt_iff (b : G.Being) (c : G.Call) :
    (G.map f).MountsAt b c ↔ G.MountsAt b c :=
  Iff.rfl

theorem map_mountsSomewhere_iff (b : G.Being) :
    (G.map f).MountsSomewhere b ↔ G.MountsSomewhere b :=
  Iff.rfl

theorem map_respondsToEveryCall_iff (b : G.Being) :
    (G.map f).RespondsToEveryCall b ↔ G.RespondsToEveryCall b :=
  Iff.rfl

theorem map_stone_iff (b : G.Being) :
    (G.map f).Stone b ↔ G.Stone b :=
  Iff.rfl

theorem map_deliveredTo_iff (deed reception : G.Weld) :
    (G.map f).DeliveredTo deed reception ↔ G.DeliveredTo deed reception :=
  Iff.rfl

theorem map_landsAt_iff (deed reception : G.Weld) :
    (G.map f).LandsAt deed reception ↔ G.LandsAt deed reception :=
  Iff.rfl

theorem map_environsLine_iff
    (b : G.Being) (deed reception : G.Weld) :
    (G.map f).EnvironsLine b deed reception ↔ G.EnvironsLine b deed reception :=
  Iff.rfl

theorem map_terminus_iff (b : G.Being) :
    (G.map f).Terminus b ↔ G.Terminus b := by
  constructor
  · intro h c r hresp
    exact (f.atBot_iff (G.grade b c r)).mp (h c r hresp)
  · intro h c r hresp
    exact (f.atBot_iff (G.grade b c r)).mpr (h c r hresp)

theorem map_liveTerminus_iff (b : G.Being) :
    (G.map f).LiveTerminus b ↔ G.LiveTerminus b := by
  constructor
  · intro h
    exact ⟨(G.map_mountsSomewhere_iff f b).mp h.left,
      (G.map_terminus_iff f b).mp h.right⟩
  · intro h
    exact ⟨(G.map_mountsSomewhere_iff f b).mpr h.left,
      (G.map_terminus_iff f b).mpr h.right⟩

theorem map_responsiveTerminus_iff (b : G.Being) :
    (G.map f).ResponsiveTerminus b ↔ G.ResponsiveTerminus b := by
  constructor
  · intro h
    exact ⟨(G.map_respondsToEveryCall_iff f b).mp h.left,
      (G.map_terminus_iff f b).mp h.right⟩
  · intro h
    exact ⟨(G.map_respondsToEveryCall_iff f b).mpr h.left,
      (G.map_terminus_iff f b).mpr h.right⟩

theorem map_atZeroSharePole_iff (b : G.Being) :
    (G.map f).AtZeroSharePole b ↔ G.AtZeroSharePole b := by
  constructor
  · intro h
    exact h.elim
      (fun hstone => Or.inl ((G.map_stone_iff f b).mp hstone))
      (fun hterm => Or.inr ((G.map_terminus_iff f b).mp hterm))
  · intro h
    exact h.elim
      (fun hstone => Or.inl ((G.map_stone_iff f b).mpr hstone))
      (fun hterm => Or.inr ((G.map_terminus_iff f b).mpr hterm))

theorem map_hasSelfPoleIndex_iff (w : G.Weld) :
    (G.map f).HasSelfPoleIndex w ↔ G.HasSelfPoleIndex w := by
  constructor
  · intro h hbot
    exact h ((f.atBot_iff (G.share w)).mpr hbot)
  · intro h hbot
    exact h ((f.atBot_iff (G.share w)).mp hbot)

theorem map_probeConstant_iff (b : G.Being) (cs : G.Call → Prop) :
    (G.map f).ProbeConstant b cs ↔ G.ProbeConstant b cs := by
  constructor
  · intro h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂
    exact (f.orderEq_iff (G.grade b c₁ r₁) (G.grade b c₂ r₂)).mp
      (h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂)
  · intro h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂
    exact (f.orderEq_iff (G.grade b c₁ r₁) (G.grade b c₂ r₂)).mpr
      (h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂)

theorem map_stateToolFits_iff (w : G.Weld) :
    (G.map f).StateToolFits w ↔ G.StateToolFits w := by
  constructor
  · intro h hidx
    exact h ((G.map_hasSelfPoleIndex_iff f w).mpr hidx)
  · intro h hidx
    exact h ((G.map_hasSelfPoleIndex_iff f w).mp hidx)

namespace Tier

/-- Transport a diagnostic tier along a grid reparameterization. -/
def map {G : Grid Contrib} (f : DisplayReparam Contrib Contrib') :
    Tier G → Tier (G.map f)
  | .floor => .floor
  | .actTime w => .actTime w

end Tier

theorem map_tier_hasNonzeroShare_iff :
    ∀ t : Tier G,
      Tier.hasNonzeroShare (G.map f) (Tier.map f t) ↔
        Tier.hasNonzeroShare G t
  | .floor => Iff.rfl
  | .actTime w => G.map_hasSelfPoleIndex_iff f w

theorem map_rePitch (before : Config Contrib) (received : G.Weld) :
    (G.map f).rePitch (before.map f) received =
      (G.rePitch before received).map f :=
  rfl

theorem map_isShareDrop_iff
    (before : Config Contrib) (received : G.Weld) :
    (G.map f).IsShareDrop (before.map f) received ↔
      G.IsShareDrop before received := by
  constructor
  · intro h
    exact ⟨(f.le_iff (G.share received) before.tendency).mpr h.left,
      fun hle => h.right ((f.le_iff before.tendency (G.share received)).mp hle)⟩
  · intro h
    exact ⟨(f.le_iff (G.share received) before.tendency).mp h.left,
      fun hle => h.right ((f.le_iff before.tendency (G.share received)).mpr hle)⟩

theorem map_landsWithShareDrop_iff
    (before : Config Contrib) (deed reception : G.Weld) :
    (G.map f).LandsWithShareDrop (before.map f) deed reception ↔
      G.LandsWithShareDrop before deed reception := by
  constructor
  · intro h
    exact ⟨(G.map_landsAt_iff f deed reception).mp h.left,
      (G.map_isShareDrop_iff f before reception).mp h.right⟩
  · intro h
    exact ⟨(G.map_landsAt_iff f deed reception).mpr h.left,
      (G.map_isShareDrop_iff f before reception).mpr h.right⟩

theorem map_releaseLine_iff
    (before : Config Contrib) (b : G.Being) (deed reception : G.Weld) :
    (G.map f).ReleaseLine (before.map f) b deed reception ↔
      G.ReleaseLine before b deed reception := by
  constructor
  · intro h
    exact ⟨(G.map_environsLine_iff f b deed reception).mp h.left,
      (G.map_isShareDrop_iff f before reception).mp h.right⟩
  · intro h
    exact ⟨(G.map_environsLine_iff f b deed reception).mpr h.left,
      (G.map_isShareDrop_iff f before reception).mpr h.right⟩

end Grid

/- ==============================================================================
   Negative example: equality-at-bottom does not transport
============================================================================== -/

namespace InvarianceNegative

inductive TwoBottom
  | chosen
  | other

instance : PreorderBot TwoBottom where
  le       := fun _ _ => True
  le_refl  := fun _ => True.intro
  le_trans := fun _ _ => True.intro
  bot      := TwoBottom.chosen
  bot_le   := fun _ => True.intro

instance : PreorderBot Unit where
  le       := fun _ _ => True
  le_refl  := fun _ => True.intro
  le_trans := fun _ _ => True.intro
  bot      := ()
  bot_le   := fun _ => True.intro

def mergeToUnit : DisplayReparam TwoBottom Unit where
  toFun _ := ()
  le_iff _ _ := ⟨fun _ => True.intro, fun _ => True.intro⟩
  atBot_bot := True.intro

def twoBottomGrid : Grid TwoBottom where
  Being      := Unit
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := TwoBottom.other
  conditions _ _ := False

/-- The old, equality-token version of terminus, kept only for this
    counterexample. It is not the system predicate. -/
def OldEqTerminus {Contrib : Type} [PreorderBot Contrib]
    (G : Grid Contrib) (b : G.Being) : Prop :=
  ∀ c r, G.respondsTo b c = some r → G.grade b c r = shareZero

example : twoBottomGrid.Terminus () :=
  fun _ _ _ => True.intro

example : ¬ OldEqTerminus twoBottomGrid () := by
  intro h
  have hbad : TwoBottom.other = TwoBottom.chosen := h () () rfl
  cases hbad

example : OldEqTerminus (twoBottomGrid.map mergeToUnit) () :=
  fun _ _ _ => rfl

/-- The new predicate transports across the merge, while the old equality-token
    predicate would hold after the merge and fail before it. -/
example :
    ((twoBottomGrid.map mergeToUnit).Terminus () ↔ twoBottomGrid.Terminus ()) ∧
      OldEqTerminus (twoBottomGrid.map mergeToUnit) () ∧
      ¬ OldEqTerminus twoBottomGrid () :=
  ⟨twoBottomGrid.map_terminus_iff mergeToUnit (),
    fun _ _ _ => rfl,
    by
      intro h
      have hbad : TwoBottom.other = TwoBottom.chosen := h () () rfl
      cases hbad⟩

end InvarianceNegative

end WAA
