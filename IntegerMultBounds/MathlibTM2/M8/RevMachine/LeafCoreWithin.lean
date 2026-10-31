module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCore
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.EmbedWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRunWithin

/-! The concrete stage-2 leaf placement inherits the complete original-header
stage-1 prefix certificate; spectators retain their heads. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCoreWithin
noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open RecursiveInterchangeLayout (Descriptor volume)
open CommonBank (bank)
open Routines (hdr)
open Family (count)
open LeafCore
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
variable [M8.Machine.Net] {T : ℕ}

theorem core_runs_within (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n)
    (roles : Tapes T prime) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (c : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime)
    (io : Fin T) {u : Descriptor} (hpos : u.Positive) (x : Fin (volume prime u) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff*volume prime u : ℕ) ≤
      (raw (bank roles (hdr u) f p node scalar c st) (count T+small)).head j ∧
      (raw (bank roles (hdr u) f p node scalar c st) (count T+small)).head j+
        (M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff*volume prime u : ℕ) ≤ hi) :
    HoareWithin (core io).program
      (· = raw (bank roles (hdr u) f p node scalar c st) (core io).tapes)
      (· = raw (bank (SharedPlacementAlphabet.setTape roles io
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd u.rows) x)) 0)
        (hdr u) f p node scalar c st) (core io).tapes)
      (M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (hdr u))
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let X := bank roles (hdr u) f p node scalar c st
  have hX := bank_role roles (hdr u) f p node scalar c st io
  have hsmall : ∀ j, lo+(M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff*volume prime u : ℕ) ≤
      (M8.Machine.ArbitraryWidthOriginalTotalRun.input (caller io X)).head j ∧
      (M8.Machine.ArbitraryWidthOriginalTotalRun.input (caller io X)).head j+
        (M8.Machine.ArbitraryWidthOriginalTotalRunWithin.coefficient cutoff*volume prime u : ℕ) ≤ hi := by
    intro j
    rw [input_eq]
    have hm := hmargin (slot io j)
    rw [(slot_read io X j).1] at hm
    exact hm
  have hrun := M8.Machine.ArbitraryWidthOriginalTotalRunWithin.runs_within cutoff hcut
    (caller io X) Fin.castSucc (Fin.last 6) u (hdr u) hpos (Routines.hdr_headers u)
    (fun i => by simp [caller,sel,X,CommonBank.bank_header,CounterDimensions.descriptorTape])
    (fun i => by simp [caller,sel,X,CommonBank.bank_header,CounterDimensions.descriptorHead])
    x (by simp only [caller,sel,Fin.lastCases_last]; rw [hX.2,hx])
    (by simp only [caller,sel,Fin.lastCases_last]; rw [hX.1,hh]) lo hi hsmall
  rw [input_eq,input_eq] at hrun
  have hframe : ∀ j : Fin (count T+small), lo ≤ (raw X (count T+small)).head j ∧
      (raw X (count T+small)).head j ≤ hi := by
    intro j
    have hm := hmargin j
    change lo+_ ≤ (raw X (count T+small)).head j ∧ (raw X (count T+small)).head j+_ ≤ hi at hm
    exact ⟨by omega,by omega⟩
  change HoareWithin stage1 _ _ _ _ at hrun
  exact Embed.place_within hrun (slot io) (slot_injective io) (Nat.add_comm small (count T)) X
    (fun j => slot_read io X j) hframe (core_runs roles f p node scalar c st io hpos x hh hx)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCoreWithin
