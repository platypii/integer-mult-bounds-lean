module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanLive
public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanPadding

/-! Execute all live and padded residual records in physical order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {T r d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def ScanData.recordTime (a : ScanData r d w W) (U : Type) (j : ℕ) :=
  let volume := M^(d+1)*W
  let branch := if LabelStock.live r (w+1) 1 j then
    6*volume+6+(1+signedResidualTime U (a.pivots j) w W a.H a.J)
    else 4*(d+1)*(d+1)+1
  branch+(4*volume+4)+((d+1)*(d+1)*(4*a.H+4)+1)

theorem residualScan_exec (a : ScanData r d w W) (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T)
    (off : ∀ i k, ports i ≠ ext k) (inputs : ℕ → Record.Array d 1 (w+1) W)
    (encoded : ∀ j < a.records, Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j)
    (signed : (Record.signedInputs a.table (w+1) a.records inputs).Forall₂ Record.Correct a.signed)
    (liveSpec : ∀ j < a.records, LabelStock.live r (w+1) 1 j = true →
      ((a.matrix j).det = 1 ∨ (a.matrix j).det = -1) ∧
      (LabelRing.res prime (w+1) (by omega)).mapMatrix (a.matrix j) = a.table (LabelStock.residue r (w+1) 1 j))
    (padding : ∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, Record.scalarArray (inputs j) = fun _ => symbol)
    (hm : M < 2^a.H) (hw : W < 2^a.J) (hW : 0 < W)
    (body : P → Pr P T columnCapacity prime U) (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (start : ScanReady a ports ext 0 S)
    (mask : S.R (ext 0) = (LabelMask.selectors r (w+1) a.records).map bitSymbol) :
    ∃ z F n, z.user = v.user ∧ ScanReady a ports ext a.records F ∧ F.R (ext 0) = [] ∧
      n ≤ ((List.range a.records).map fun j => a.recordTime U j + 4).sum + 2 ∧
      Exec body (residualScan ports (ext 0) (ext 1) (ext 2) (ext 3) (ext 4) (ext 5) d) (mk v S) n (mk z F) := by
  unfold residualScan
  apply maskedRange_exec body _ _ _ a.records (LabelStock.live r (w+1) 1) (a.recordTime U) (ScanReady a ports ext)
    (fun _ _ bits h => h.mask (fun i => off i 0) bits) _ v S start
    (by simpa [LabelMask.selectors,List.map_map,Function.comp_def] using mask)
  intro j inside u D ready
  cases h : LabelStock.live r (w+1) 1 j with
  | false =>
    obtain ⟨symbol,constant⟩ := padding j inside h
    simpa [ScanData.recordTime,h] using ready.padding a ports ext off j inside h inputs (encoded j inside)
      symbol constant signed body u D
  | true =>
    obtain ⟨det,lift⟩ := liveSpec j inside h
    simpa [ScanData.recordTime,h] using ready.live a ports ext off j inside h det lift inputs (encoded j inside)
      signed hm hw hW body u D

end IntegerMultBounds.MathlibTM2.Cover.Fallback
