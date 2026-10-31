module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegment
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSegmentSpace
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.EmbedSpace

/-! Every actual prefix of a segment placed on the node bank stays within one
active-volume allowance of each initial head, including retained spectators. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegment
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open CommonBank (bank K)
open FlatCoordinateSchedule (bits)
open SharedBankStageInput (raw)
noncomputable section
variable {t m f b T' : ℕ}

def segmentSpace (wire : Fin t) (l : List (AtomRoleSegment.SOp m)) (f V : ℕ) : ℕ :=
  AtomRoleSegment.chainSpace wire l*V+(bits (f-1)).length+2

theorem segment_heads (hT : t+15 ≤ T') (wire : Fin t)
    (l : List (AtomRoleSegment.SOp m)) (hfit : ∀ s ∈ l, AtomRoleSegment.tapesOf wire s ≤ T')
    (hb : 0 < b) (hf : 0 < f) (v : Descriptor) (hw : v.width = (m*f)*b) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (fs : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (c : Fin K → Option ℕ) (st : Tapes 2 prime) (hc : SegCounters c b f)
    (data : RecursiveViewedAction.Data t v) :
    let initial := raw (bank (RecursiveRoleSerialization.roles data) hs fs p node scalar c st)
      (CommonBank.count t+(T'+2))
    ∀ {z}, RunInvariant (place (AtomRoleSegment.chain T' wire l hfit).2 hT).program (· = initial) z →
      ∀ i, initial.head i-(segmentSpace wire l f (volume prime v) : ℕ) ≤ z.head i ∧
        z.head i ≤ initial.head i+(segmentSpace wire l f (volume prime v) : ℕ) := by
  intro initial z hz
  obtain ⟨u,hu,n,hr⟩ := hz
  subst u
  apply Embed.place_heads (AtomRoleSegment.chain T' wire l hfit).2
    (AtomRoleRun.common T' hs f b data) (segSlot t T') (segSlot_injective hT) (Nat.add_comm _ _)
    (bank (RecursiveRoleSerialization.roles data) hs fs p node scalar c st)
    (seg_read hT hs hc data) (segmentSpace wire l f (volume prime v)) ?_ hr
  intro y hy i
  have hh := AtomRoleSegment.chain_heads hb T' hf wire v hw hp hs hv l hfit data hy i
  have hb := AtomRoleRun.loopBank_heads T' hs f data (AtomRoleInstall.rest b) i
  change 0 ≤ (AtomRoleRun.common T' hs f b data).head i ∧
    (AtomRoleRun.common T' hs f b data).head i ≤ 1 at hb
  dsimp only [segmentSpace]
  omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegment
