module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegmentSpace

/-! The actual node segment block, including atom families, gates and reset,
has a workspace allowance linear in its active role volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open NodeBank (tapes wireSlot io)
open CommonBank (bank K)
open Schedule (Seg)
open SharedBankStageInput (raw)
open AtomRolePlan (Fits)
noncomputable section
variable (N : RevNetwork)

open Classical in
def segSpaceConstant : Seg (N.World ⊕ N.Temp) N.width → ℕ
  | .edge w ops =>
    if h : ∀ o ∈ AtomSegment.atoms ops, Fits N.width o then
      AtomRoleSegment.chainSpace (wireSlot N w) (AtomRoleSegment.sops ops h)+3
    else Machine.RoleOpsClean.coefficient (t := tapes N) []
  | .gate g => Machine.RoleOpsClean.coefficient (gateOp N g)
  | .reset w => Machine.RoleOpsClean.coefficient
      [.fill ⟨io N,wireSlot N w,(NodeBank.wireSlot_ne_io N w).symm⟩ NodeSplit.zeroBit]

theorem seg_heads (s : Seg (N.World ⊕ N.Temp) N.width)
    {b f : ℕ} (hb : 0 < b) (hf : 0 < f) (v : Descriptor)
    (hw : v.width = (N.width*f)*b) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (fs : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (c : Fin K → Option ℕ) (st : Tapes 2 prime) (hc : NodeSegment.SegCounters c b f)
    (data : RecursiveViewedAction.Data (tapes N) v) :
    let initial := raw (bank (RecursiveRoleSerialization.roles data) hs fs p node scalar c st) (segB N s).tapes
    ∀ z : Config (segB N s).tapes (segB N s).states prime,
      RunInvariant (segB N s).program (· = initial) z →
      ∀ i, initial.head i-(segSpaceConstant N s*volume prime v : ℕ) ≤ z.head i ∧
        z.head i ≤ initial.head i+(segSpaceConstant N s*volume prime v : ℕ) := by
  cases s with
  | edge w ops =>
    classical
    by_cases hfits : ∀ o ∈ AtomSegment.atoms ops, Fits N.width o
    · have hsb : segB N (.edge w ops) =
          NodeSegment.place (AtomRoleSegment.chain (segT N w (AtomRoleSegment.sops ops hfits))
            (wireSlot N w) (AtomRoleSegment.sops ops hfits) (segT_ge N w _)).2 (segT_le N w _) := by
        dsimp only [segB]
        rw [dite_eq_left hfits]
      rw [hsb]
      dsimp only [segSpaceConstant]
      rw [dite_eq_left hfits]
      intro z hz i
      let initial := raw (bank (RecursiveRoleSerialization.roles data) hs fs p node scalar c st)
        (NodeSegment.place (AtomRoleSegment.chain (segT N w (AtomRoleSegment.sops ops hfits))
          (wireSlot N w) (AtomRoleSegment.sops ops hfits) (segT_ge N w _)).2 (segT_le N w _)).tapes
      have h := NodeSegment.segment_heads (segT_le N w _) (wireSlot N w) _ (segT_ge N w _)
        hb hf v hw hp hs hv fs p node scalar c st hc data hz i
      have hV := AtomRoleCost.atoms_lt_volume hb v hw hp
      have hfV : f ≤ volume prime v :=
        (Nat.le_mul_of_pos_left f (by have := N.two_le_width; omega)).trans hV.le
      have hbits := CounterSteps.bits_length (f-1)
      change initial.head i-(AtomRoleSegment.chainSpace (wireSlot N w) (AtomRoleSegment.sops ops hfits)*volume prime v+
        (FlatCoordinateSchedule.bits (f-1)).length+2 : ℕ) ≤ z.head i ∧
        z.head i ≤ initial.head i+(AtomRoleSegment.chainSpace (wireSlot N w) (AtomRoleSegment.sops ops hfits)*volume prime v+
          (FlatCoordinateSchedule.bits (f-1)).length+2 : ℕ) at h
      change initial.head i-((AtomRoleSegment.chainSpace (wireSlot N w) (AtomRoleSegment.sops ops hfits)+3)*volume prime v : ℕ) ≤ z.head i ∧
        z.head i ≤ initial.head i+((AtomRoleSegment.chainSpace (wireSlot N w) (AtomRoleSegment.sops ops hfits)+3)*volume prime v : ℕ)
      simp only [Nat.add_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      omega
    · have hsb : segB N (.edge w ops) = NodeBank.ops [] := by
        dsimp only [segB]
        rw [dite_eq_right hfits]
      rw [hsb]
      dsimp only [segSpaceConstant]
      rw [dite_eq_right hfits]
      intro z hz
      exact RunInvariant.heads_eq (NodeBank.ops_runs [] hv hp data fs p node scalar c st) hz
  | gate g =>
    simp only [segB,segSpaceConstant]
    intro z hz
    exact RunInvariant.heads_eq (NodeBank.ops_runs (gateOp N g) hv hp data fs p node scalar c st) hz
  | reset w =>
    simp only [segB,segSpaceConstant]
    intro z hz
    exact RunInvariant.heads_eq (NodeBank.ops_runs
      [.fill ⟨io N,wireSlot N w,(NodeBank.wireSlot_ne_io N w).symm⟩ NodeSplit.zeroBit]
      hv hp data fs p node scalar c st) hz

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode
