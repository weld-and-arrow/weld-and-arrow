/-
================================================================================
  WeldAndArrow.Doctrines.FaithNegative
  The two-obscurations separator and non-vacuity witness
================================================================================

The countermodel is the undefiled-nescience witness: effective functioning and
universal shortfall closure do not remove cognitive obscuration. Under total
occurrence fidelity the buddha has `WaaEffectiveTerminus` but lacks
`WaaNoDelusion`, and therefore lacks the two-obscurations bundle
`WaaFullyEnlightened`.
-/

import WeldAndArrow.Doctrines.Faith

namespace WAA

namespace FaithNegative

open Grid
open Grid.DirectedConvention

inductive Being
  | buddha
  | disciple
  | receiver

inductive Call
  | call

inductive Response
  | response

/-- A grid in which the buddha is an effective terminus for free: its own deeds are
    never delivered, so shortfall closure for its own deeds is vacuous. The
    disciple's deed is delivered to a receiver whose live share does not drop. -/
def grid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade b _ _ :=
    match b with
    | .buddha   => 0
    | .disciple => 1
    | .receiver => 1
  conditions deed reception :=
    deed.agent = Being.disciple ∧ reception.agent = Being.receiver

def liveBefore : Config Nat :=
  { tendency := 1 }

def discipleDeed : grid.Weld :=
  ⟨Being.disciple, Call.call, Response.response⟩

def reception : grid.Weld :=
  ⟨Being.receiver, Call.call, Response.response⟩

def buddhaWeld : grid.Weld :=
  ⟨Being.buddha, Call.call, Response.response⟩

theorem liveBefore_not_atBot :
    ¬ AtBot liveBefore.tendency := by
  intro h
  exact Nat.not_succ_le_zero 0 h

theorem delivered :
    DeliveredTo grid discipleDeed reception :=
  ⟨rfl, rfl⟩

theorem buddhaWeld_actual :
    grid.Actual buddhaWeld :=
  rfl

theorem buddha_responsiveTerminus :
    grid.ResponsiveTerminus Being.buddha := by
  constructor
  · intro _c
    exact ⟨Response.response, rfl⟩
  · intro _c _r _hresp
    exact Nat.le_refl 0

/-- The buddha's own deeds are never delivered in this grid, so the shortfall
    closure conjunct holds vacuously. -/
theorem buddha_waaEffectiveTerminus :
    WaaEffectiveTerminus grid Being.buddha := by
  refine ⟨buddha_responsiveTerminus, ?_⟩
  intro before deed reception hdeed _hlive hdel
  obtain ⟨hdisciple, _hreceiver⟩ := hdel
  rw [hdeed] at hdisciple
  exact Being.noConfusion hdisciple

theorem not_hasShareDropLanding :
    ¬ HasShareDropLanding grid liveBefore discipleDeed := by
  rintro ⟨received, hland⟩
  have hreceiver : received.agent = Being.receiver := hland.left.left.right
  have hdrop : Strict (grid.share received) liveBefore.tendency :=
    hland.right
  have hstrict : Strict (1 : Nat) 1 := by
    simpa [grid, Grid.share, liveBefore, hreceiver] using hdrop
  exact strict_irrefl (1 : Nat) hstrict

/-- The buddha's recorded path claim about the disciple's deed is false: the
    delivered deed does not land as a share-drop for the live receiver context. -/
def falseClaim : RecordedUtterance grid (waaPathClaimLanguage grid) where
  weld      := buddhaWeld
  actual    := buddhaWeld_actual
  offeredAt := Tier.actTime buddhaWeld
  content   := ⟨liveBefore, discipleDeed, reception⟩

theorem falseClaim_not_fitsOfferedTier :
    ¬ falseClaim.FitsOfferedTier := by
  intro hfit
  change (waaPathClaimLanguage grid).TrueAt falseClaim.offeredAt
    falseClaim.content at hfit
  dsimp [waaPathClaimLanguage, ClaimLanguage.TrueAt, falseClaim,
    ShortfallClosedAt] at hfit
  exact not_hasShareDropLanding (hfit liveBefore_not_atBot delivered)

/-- Every attributed occurrence is treated as faithful in the separating
    model, so the character conjunct cannot evade the counterexample by a
    sealed channel. -/
def totalFidelity :
    RecordedUtterance grid (waaPathClaimLanguage grid) → Prop :=
  fun _ => True

theorem falseClaim_misfitsOfferedTier :
    falseClaim.MisfitsOfferedTier :=
  ⟨buddhaWeld, rfl, falseClaim_not_fitsOfferedTier⟩

/-- Effective termination does not remove undefiled nescience: under total
    fidelity the attributed false claim refutes no-delusion. -/
theorem buddha_not_waaNoDelusion :
    ¬ WaaNoDelusion grid totalFidelity Being.buddha := by
  intro hno
  exact falseClaim_not_fitsOfferedTier
    (hno falseClaim rfl trivial buddhaWeld rfl)

/-- The two-obscurations separator. Removal of the afflictive obscuration,
    represented by `WaaEffectiveTerminus`, does not by itself remove the
    cognitive obscuration represented by `WaaNoDelusion`. -/
theorem effectiveTerminus_not_waaFullyEnlightened :
    WaaEffectiveTerminus grid Being.buddha ∧
      ¬ WaaFullyEnlightened grid totalFidelity Being.buddha := by
  refine ⟨buddha_waaEffectiveTerminus, ?_⟩
  intro hfull
  exact buddha_not_waaNoDelusion hfull.noDelusion

/-- Doctrinal name for the same undefiled-nescience witness. -/
theorem aklishta_ajnana_witness :
    WaaEffectiveTerminus grid Being.buddha ∧
      ¬ WaaNoDelusion grid totalFidelity Being.buddha :=
  ⟨buddha_waaEffectiveTerminus, buddha_not_waaNoDelusion⟩

/-- A faithful, fitting, act-time own-deed claim for the non-vacuity witness. -/
def faithfulClaim : RecordedUtterance grid (waaPathClaimLanguage grid) where
  weld := buddhaWeld
  actual := buddhaWeld_actual
  offeredAt := Tier.actTime buddhaWeld
  content := ⟨liveBefore, buddhaWeld, reception⟩

theorem faithfulClaim_fitsOfferedTier :
    faithfulClaim.FitsOfferedTier :=
  fitsOfferedTier_of_waaEffectiveTerminus_ownDeed grid
    buddha_waaEffectiveTerminus faithfulClaim rfl buddhaWeld rfl

/-- Concrete fidelity that records exactly fitting occurrences. -/
def fittingFidelity :
    RecordedUtterance grid (waaPathClaimLanguage grid) → Prop :=
  fun u => u.FitsOfferedTier

theorem buddha_waaNoDelusion_fittingFidelity :
    WaaNoDelusion grid fittingFidelity Being.buddha := by
  intro u _hagent hfit _w _hoff
  exact hfit

/-- The full bundle is non-vacuously inhabited: one faithful, fitting,
    act-time utterance accompanies the two conjuncts. -/
theorem waaFullyEnlightened_faithful_actTime_inhabited :
    WaaFullyEnlightened grid fittingFidelity Being.buddha ∧
      ∃ u : RecordedUtterance grid (waaPathClaimLanguage grid),
        fittingFidelity u ∧
          (∃ w : grid.Weld, u.offeredAt = Tier.actTime w) ∧
            u.FitsOfferedTier := by
  refine ⟨⟨buddha_waaEffectiveTerminus,
    buddha_waaNoDelusion_fittingFidelity⟩, faithfulClaim, ?_, ?_, ?_⟩
  · exact faithfulClaim_fitsOfferedTier
  · exact ⟨buddhaWeld, rfl⟩
  · exact faithfulClaim_fitsOfferedTier

end FaithNegative

end WAA
