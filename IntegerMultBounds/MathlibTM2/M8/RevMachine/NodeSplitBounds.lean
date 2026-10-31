module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSplit
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.FamilyControlBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CounterCostBounds

/-! Generated views supply one shared size certificate for splitting and
merging. Their concrete runtime bounds are linear in active volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSplit
open IntegerMultBounds IntegerMultBounds.Machine Networks
  Networks.Shared50ModularControl RecursiveInterchangeLayout FlatCoordinateSchedule Routines
noncomputable section

structure ViewBounds (N : RevNetwork) (v : Descriptor) (b n : ℕ) : Prop where
  positive : 1 ≤ volume prime v
  atoms : n ≤ volume prime v
  mid : volume prime (midView N b n v) = volume prime v
  role : volume prime (roleView N b n v) ≤ volume prime v
  midPos : (midView N b n v).Positive
  rolePos : (roleView N b n v).Positive
  parentHeaders : ∀ i, (hdr v i).length ≤ 2*volume prime v
  middleHeaders : ∀ i, (hdr (midView N b n v) i).length ≤ 2*volume prime v
  roleHeaders : ∀ i, (hdr (roleView N b n v) i).length ≤ 2*volume prime v

theorem viewBounds (N : RevNetwork) (v : Descriptor) (hv : v.Positive) (b n : ℕ)
    (hb : 0 < b) (hw : v.width = n*b) (hd : N.roleCount ∣ v.rows) : ViewBounds N v b n := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hv
  have hsquare := Family.width_square_le_volume v hv
  have hn : n ≤ volume prime v := (Nat.le_mul_of_pos_right n hb).trans (by rw [←hw]; nlinarith only [hsquare])
  have hmid := mid_volume N hw
  have hroles := roleCount_pos N hv hd
  have hsplit := RecursiveInterchangeLayout.role_volume_mul prime N.roleCount (midView N b n v) hd
  have hrole : volume prime (roleView N b n v) ≤ volume prime v := by
    rw [←hmid,←hsplit]
    exact Nat.le_mul_of_pos_right _ hroles
  have hmp := mid_positive N (b := b) (n := n) hv
  have hrp := roleView_positive N (b := b) (n := n) hv hd
  refine ⟨hV,hn,hmid,hrole,hmp,hrp,?_,?_,?_⟩
  · exact fun i => RecursiveRowsNode.header_length _ hv _ (hdr_headers _) i
  · intro i
    have h := RecursiveRowsNode.header_length _ hmp _ (hdr_headers _) i
    rwa [hmid] at h
  · intro i
    have h := RecursiveRowsNode.header_length _ hrp _ (hdr_headers _) i
    omega

theorem splitCountersCost_linear (n m V : ℕ) (hn : n ≤ V) (hV : 1 ≤ V) :
    splitCountersCost n m ≤ (2*BinaryDescriptorDivMod.linearConstant (bits m)+300)*V := by
  have hdiv := Nat.mul_le_mul_left (BinaryDescriptorDivMod.linearConstant (bits m))
    (show n+1 ≤ 2*V by omega)
  have hf := Nat.div_le_self n m
  have hmf := Nat.mul_div_le n m
  have hlen := RevBudget.bits_len (n/m)
  have hz : (bits 0).length = 0 := rfl
  unfold splitCountersCost
  rw [hz]
  nlinarith only [hdiv,hf,hmf,hlen,hn,hV]

def splitSpaceConstant (N : RevNetwork) : ℕ :=
  2*BinaryDescriptorDivMod.linearConstant (bits N.width)+10000+
    (74+RecursiveRowsNode.rowConstant N.roleCount+RecursiveRowsNodeRoleBank.constant N.roleCount)+
    M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N zeroBit)

theorem splitCost_linear (N : RevNetwork) (v : Descriptor) (hv : v.Positive) (b n : ℕ)
    (hb : 0 < b) (hw : v.width = n*b) (hd : N.roleCount ∣ v.rows) :
    splitCost (N := N) v b n ≤ splitSpaceConstant N*volume prime v := by
  have s := viewBounds N v hv b n hb hw hd
  have hcounter := splitCountersCost_linear n N.width (volume prime v) s.atoms s.positive
  have hpush := RecursiveViewFrame.pushCost_le (hdr v) _ s.parentHeaders
  have hrow := RecursiveRowsNode.entry_cost_linear (c := N.roleCount) _ s.midPos _ (hdr_headers _)
  rw [s.mid] at hrow
  have hlen (x : ℕ) (hx : x ≤ n) : (bits x).length ≤ 2*volume prime v := by
    have h := RevBudget.bits_len x
    have hn := s.atoms
    have hV := s.positive
    omega
  have h0 := hlen n le_rfl
  have h1 := hlen (n % N.width) (Nat.mod_le _ _)
  have h2 := hlen (N.width*(n/N.width)) (Nat.mul_div_le _ _)
  have hz : (bits 0).length = 0 := rfl
  have hops := Nat.mul_le_mul_left
    (M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N zeroBit)) s.role
  have hV := s.positive
  unfold splitCost splitSpaceConstant
  rw [hz,s.mid]
  nlinarith only [hcounter,hpush,hrow,h0,h1,h2,hops,hV]

theorem mergeCountersCost_linear (v : Descriptor) (hv : v.Positive) (b n m : ℕ)
    (hb : 0 < b) (hn : 1 ≤ n) (hw : v.width = n*b) :
    mergeCountersCost b n m ≤ (4100+BinaryDescriptorDivMod.linearConstant (bits m))*volume prime v := by
  have hp := Family.prepCost_linear v hv b m n hb hn hw
  have hsquare := Family.width_square_le_volume v hv
  have hnV : n ≤ volume prime v := (Nat.le_mul_of_pos_right n hb).trans (by rw [←hw]; nlinarith only [hsquare])
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hv
  have hlen (x : ℕ) (hx : x ≤ n) : (bits x).length ≤ 2*volume prime v := by
    have h := RevBudget.bits_len x
    omega
  have h0 := hlen (n/m) (Nat.div_le_self _ _)
  have h1 := hlen (n/m-1) (by have h := Nat.div_le_self n m; omega)
  have h2 := hlen (n % m) (Nat.mod_le _ _)
  unfold mergeCountersCost
  unfold Family.prepCost at hp
  nlinarith only [hp,h0,h1,h2,hV]

def mergeSpaceConstant (N : RevNetwork) : ℕ :=
  BinaryDescriptorDivMod.linearConstant (bits N.width)+10000+
    (128+RecursiveRowsNode.rowConstant N.roleCount)+
    M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N blank)

theorem mergeCost_linear (N : RevNetwork) (v : Descriptor) (hv : v.Positive) (b n : ℕ)
    (hb : 0 < b) (hn : 1 ≤ n) (hw : v.width = n*b) (hd : N.roleCount ∣ v.rows) :
    mergeCost (N := N) v b n ≤ mergeSpaceConstant N*volume prime v := by
  have s := viewBounds N v hv b n hb hw hd
  have hcounter := mergeCountersCost_linear v hv b n N.width hb hn hw
  have hrow := RecursiveRowsNode.exit_cost_linear (c := N.roleCount) _ s.midPos (roleCount_pos N hv hd) hd
    _ _ (hdr_headers _) (hdr_headers _)
  rw [s.mid] at hrow
  have hrestore := RecursiveViewFrame.restoreCost_le (hdr v) (hdr (midView N b n v)) _ s.parentHeaders s.middleHeaders
  have hops := Nat.mul_le_mul_left
    (M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N blank)) s.role
  have hV := s.positive
  unfold mergeCost mergeSpaceConstant
  rw [s.mid]
  nlinarith only [hcounter,hrow,hrestore,hops,hV]

/-- All-prefix head bounds for the actual split from the parent stream. -/
theorem split_heads (N : RevNetwork) (v : Descriptor) (hv : v.Positive) (b n : ℕ)
    (hb : 0 < b) (hw : v.width = n*b) (hn : N.width ≤ n) (hd : N.roleCount ∣ v.rows)
    (x : Fin (volume prime v) → Fin 4) (fs : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    let initial := CommonBank.bank (NodePark.childRoles N (RecursiveShiftRoleBank.source x))
      (hdr v) fs p node scalar (Family.leafC b N.width n 0) st
    ∀ {c : Config (splitB N).tapes (splitB N).states prime},
      RunInvariant (splitB N).program (· = SharedBankStageInput.raw initial (splitB N).tapes) c →
      ∀ i, (SharedBankStageInput.raw initial (splitB N).tapes).head i-(splitSpaceConstant N*volume prime v : ℕ) ≤ c.head i ∧
        c.head i ≤ (SharedBankStageInput.raw initial (splitB N).tapes).head i+(splitSpaceConstant N*volume prime v : ℕ) := by
  dsimp only
  intro c hc
  have h := split_runs_data (N := N) (fs := fs) (p := p) (node := node) (scalar := scalar) (st := st)
    hv hb hw hn hd x
  have h' := h.consequence (fun _ h => h) (fun _ h => h) (splitCost_linear N v hv b n hb hw hd)
  exact hc.heads_eq h'

/-- All-prefix head bounds for the actual merge, using the mathematical role
invariant maintained by the node's schedule. -/
theorem merge_heads (N : RevNetwork) (v : Descriptor) (hv : v.Positive) (b n : ℕ)
    (hb : 0 < b) (hn : 1 ≤ n) (hw : v.width = n*b) (hd : N.roleCount ∣ v.rows)
    (data : RecursiveMixedSchedule.Data (NodeBank.tapes N) (roleView N b n v)) (hinv : NodeInv N data)
    (fs : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (hfree : Family.NodeFree node) :
    let initial := CommonBank.bank (RecursiveRoleSerialization.roles data) (hdr (roleView N b n v)) fs p
      (RecursiveViewFrame.savedStack (hdr (midView N b n v)) (RecursiveViewFrame.savedStack (hdr v) node))
      scalar (NodeCall.nodeC N b (n/N.width)) st
    ∀ {c : Config (mergeB N).tapes (mergeB N).states prime},
      RunInvariant (mergeB N).program (· = SharedBankStageInput.raw initial (mergeB N).tapes) c →
      ∀ i, (SharedBankStageInput.raw initial (mergeB N).tapes).head i-(mergeSpaceConstant N*volume prime v : ℕ) ≤ c.head i ∧
        c.head i ≤ (SharedBankStageInput.raw initial (mergeB N).tapes).head i+(mergeSpaceConstant N*volume prime v : ℕ) := by
  dsimp only
  intro c hc
  obtain ⟨x,hx,h⟩ := merge_runs (N := N) (fs := fs) (p := p) (node := node) (scalar := scalar) (st := st)
    hv hb hw hd data hinv hfree
  have h' := h.consequence (fun _ h => h) (fun _ h => h) (mergeCost_linear N v hv b n hb hn hw hd)
  exact hc.heads_eq h'

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSplit
